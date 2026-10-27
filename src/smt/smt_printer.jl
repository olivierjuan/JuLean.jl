# JuLean.jl - SMT-LIB 2.6 Generator

"""
    julia_to_smt_type(t) -> String

Maps a Julia type or type symbol to its SMT-LIB sort (`Real`, `Int`, `Bool`, datatypes, or arrays).
"""
function julia_to_smt_type(t)::String
    if haskey(STRUCT_REGISTRY, t) || (t isa Symbol && haskey(STRUCT_REGISTRY, t))
        return string(t)
    elseif t in (:Int, :Int64, :Int32, :Integer, Int, Int64, Int32, Integer)
        return "Int"
    elseif t in (:Bool, Bool)
        return "Bool"
    elseif t isa Expr && t.head == :curly
        base = t.args[1]
        if base in (:Vector, :Array)
            elem = length(t.args) >= 2 ? julia_to_smt_type(t.args[2]) : "Real"
            return "(Array Int $elem)"
        elseif base == :Rational
            return "Real"
        end
    elseif t isa LeanType
        if t isa LeanInt || t isa LeanNat
            return "Int"
        elseif t isa LeanBool
            return "Bool"
        elseif t isa LeanArray
            return "(Array Int $(julia_to_smt_type(t.elem_type)))"
        elseif t isa LeanNamedType
            return t.name
        else
            return "Real"
        end
    end
    # Default to Real (exact QF_LRA / QF_NRA arithmetic)
    return "Real"
end

"""
Unwraps single-statement blocks and returns, discarding LineNumberNodes.
"""
function unwrap_smt_expr(ex)
    if ex isa Expr && ex.head == :block
        clean_args = filter(a -> !(a isa LineNumberNode), ex.args)
        if isempty(clean_args)
            return true
        elseif length(clean_args) == 1
            return unwrap_smt_expr(clean_args[1])
        end
    elseif ex isa Expr && ex.head == :return
        return isempty(ex.args) ? true : unwrap_smt_expr(ex.args[1])
    end
    return ex
end

"""
    julia_to_smt_expr(ex) -> String

Recursively translates a Julia expression or literal into an SMT-LIB 2.6 s-expression string.
"""
function julia_to_smt_expr(ex)::String
    unwrapped = unwrap_smt_expr(ex)

    if unwrapped isa Integer
        return unwrapped < 0 ? "(- $(abs(unwrapped)))" : string(unwrapped)
    elseif unwrapped isa Rational
        num_str = numerator(unwrapped) < 0 ? "(- $(abs(numerator(unwrapped))))" : string(numerator(unwrapped))
        den_str = string(denominator(unwrapped))
        return "(/ $num_str.0 $den_str.0)"
    elseif unwrapped isa AbstractFloat
        r = rationalize(BigInt, unwrapped)
        if denominator(r) == 1
            num_str = numerator(r) < 0 ? "(- $(abs(numerator(r))))" : string(numerator(r))
            return "$num_str.0"
        else
            num_str = numerator(r) < 0 ? "(- $(abs(numerator(r))))" : string(numerator(r))
            den_str = string(denominator(r))
            return "(/ $num_str.0 $den_str.0)"
        end
    elseif unwrapped isa Bool
        return unwrapped ? "true" : "false"
    elseif unwrapped isa Symbol
        return string(unwrapped)
    elseif !(unwrapped isa Expr)
        return string(unwrapped)
    end

    e = unwrapped::Expr

    # Block expression: clean LineNumberNodes
    if e.head == :block
        clean_args = filter(a -> !(a isa LineNumberNode), e.args)
        if isempty(clean_args)
            return "true"
        elseif length(clean_args) == 1
            return julia_to_smt_expr(clean_args[1])
        else
            return build_smt_let_block(clean_args)
        end
    elseif e.head == :return
        return isempty(e.args) ? "true" : julia_to_smt_expr(e.args[1])
    elseif e.head in (:if, :elseif)
        cond = julia_to_smt_expr(e.args[1])
        then_b = julia_to_smt_expr(e.args[2])
        else_b = if length(e.args) >= 3
            julia_to_smt_expr(e.args[3])
        else
            "true"
        end
        return "(ite $cond $then_b $else_b)"
    elseif e.head in (:&&, :and)
        left = julia_to_smt_expr(e.args[1])
        right = julia_to_smt_expr(e.args[2])
        return "(and $left $right)"
    elseif e.head in (:||, :or)
        left = julia_to_smt_expr(e.args[1])
        right = julia_to_smt_expr(e.args[2])
        return "(or $left $right)"
    elseif e.head == :comparison
        return translate_smt_comparison(e.args)
    elseif e.head in (Symbol("-->"), Symbol("⟹"))
        left = julia_to_smt_expr(e.args[1])
        right = julia_to_smt_expr(e.args[2])
        return "(=> $left $right)"
    elseif e.head == :. && length(e.args) == 2
        # Field access: obj.field -> (field obj)
        obj = julia_to_smt_expr(e.args[1])
        fld = e.args[2] isa QuoteNode ? e.args[2].value : e.args[2]
        return "($fld $obj)"
    elseif e.head == :ref && length(e.args) >= 2
        # Array access: arr[i] -> (select arr i)
        coll = julia_to_smt_expr(e.args[1])
        idx = julia_to_smt_expr(e.args[2])
        return "(select $coll $idx)"
    elseif e.head == :macrocall
        return translate_smt_macro(e)
    elseif e.head == :call
        return translate_smt_call(e.args)
    else
        return string(ex)
    end
end

"""
Translates supported macros (like @forall, @exists) into SMT-LIB quantifier expressions.
"""
function translate_smt_macro(e::Expr)::String
    mname = e.args[1]
    sym = mname isa Symbol ? mname : (mname isa GlobalRef ? mname.name : nothing)
    clean_args = filter(a -> !(a isa LineNumberNode), e.args[2:end])

    if sym in (Symbol("@forall"), Symbol("@exists")) && length(clean_args) >= 2
        binding = clean_args[1]
        cond_smt = julia_to_smt_expr(clean_args[2])
        quant = (sym == Symbol("@forall")) ? "forall" : "exists"

        # Form: i in a:b
        if binding isa Expr && binding.head == :call && binding.args[1] in (:in, :∈) && length(binding.args) == 3
            var_name = string(binding.args[2])
            rng = binding.args[3]
            if rng isa Expr && rng.head == :call && rng.args[1] == :(:) && length(rng.args) == 3
                a_smt = julia_to_smt_expr(rng.args[2])
                b_smt = julia_to_smt_expr(rng.args[3])
                bounds = "(and (<= $a_smt $var_name) (<= $var_name $b_smt))"
                inner = (quant == "forall") ? "(=> $bounds $cond_smt)" : "(and $bounds $cond_smt)"
                return "($quant (($var_name Int)) $inner)"
            else
                return "($quant (($var_name Int)) $cond_smt)"
            end
        elseif binding isa Expr && binding.head == :(::)
            var_name = string(binding.args[1])
            sort_str = julia_to_smt_type(binding.args[2])
            return "($quant (($var_name $sort_str)) $cond_smt)"
        elseif binding isa Symbol
            var_name = string(binding)
            return "($quant (($var_name Real)) $cond_smt)"
        end
    end

    return string(e)
end

"""
Translate a block of let assignments into SMT `let` expressions.
"""
function build_smt_let_block(stmts::Vector{Any})::String
    if isempty(stmts)
        return "true"
    end
    stmt = stmts[1]
    rest = stmts[2:end]

    if stmt isa Expr && stmt.head == :(=) && length(stmt.args) == 2
        var_name = string(stmt.args[1])
        val = julia_to_smt_expr(stmt.args[2])
        body = isempty(rest) ? var_name : build_smt_let_block(rest)
        return "(let (($var_name $val)) $body)"
    elseif stmt isa Expr && stmt.head == :return
        return julia_to_smt_expr(stmt.args[1])
    else
        curr = julia_to_smt_expr(stmt)
        return isempty(rest) ? curr : build_smt_let_block(rest)
    end
end

"""
Translate function calls and operators to SMT-LIB format.
"""
function translate_smt_call(args::Vector{Any})::String
    fn = args[1]
    fn_sym = fn isa Symbol ? fn : (fn isa GlobalRef ? fn.name : nothing)

    # Struct constructor: Interval(a, b) -> (mk-Interval a b)
    if fn_sym !== nothing && haskey(STRUCT_REGISTRY, fn_sym)
        call_args = join([julia_to_smt_expr(a) for a in args[2:end]], " ")
        return "(mk-$fn_sym $call_args)"
    end

    # Length / size: length(a) -> (size a)
    if fn_sym in (:length, :size) && length(args) == 2
        return "(size $(julia_to_smt_expr(args[2])))"
    end

    if fn_sym in (:+, :-, :*, :/)
        if length(args) == 3
            op = string(fn_sym)
            l = julia_to_smt_expr(args[2])
            r = julia_to_smt_expr(args[3])
            return "($op $l $r)"
        elseif length(args) == 2 && fn_sym == :-
            return "(- $(julia_to_smt_expr(args[2])))"
        end
    elseif fn_sym in (:(==), :eq)
        return "(= $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:!=, :≠)
        return "(distinct $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:<, :lt)
        return "(< $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:<=, :≤, :le)
        return "(<= $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:>, :gt)
        return "(> $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:>=, :≥, :ge)
        return "(>= $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:!, :¬)
        return "(not $(julia_to_smt_expr(args[2])))"
    elseif fn_sym in (:implies, :⟹, Symbol("-->"))
        return "(=> $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:&&, :and)
        return "(and $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    elseif fn_sym in (:||, :or)
        return "(or $(julia_to_smt_expr(args[2])) $(julia_to_smt_expr(args[3])))"
    end

    # Generic function application
    call_args = join([julia_to_smt_expr(a) for a in args[2:end]], " ")
    return "($fn_sym $call_args)"
end

"""
Translate chained comparisons (`a <= b <= c`) to conjunctions of SMT comparisons.
"""
function translate_smt_comparison(args::Vector{Any})::String
    terms = String[]
    for i in 2:2:length(args)
        op = args[i]
        op_smt = if op in (:(==), :eq)
            "="
        elseif op in (:!=, :≠)
            "distinct"
        elseif op in (:<=, :≤, :le)
            "<="
        elseif op in (:<, :lt)
            "<"
        elseif op in (:>=, :≥, :ge)
            ">="
        elseif op in (:>, :gt)
            ">"
        else
            string(op)
        end
        l = julia_to_smt_expr(args[i-1])
        r = julia_to_smt_expr(args[i+1])
        push!(terms, "($op_smt $l $r)")
    end
    if length(terms) == 1
        return terms[1]
    else
        return "(and " * join(terms, " ") * ")"
    end
end

"""
Checks whether an expression AST contains quantifier macro calls (@forall, @exists).
"""
function has_quantifier(e)::Bool
    if e isa Expr
        if e.head == :macrocall && length(e.args) >= 1
            mname = e.args[1]
            sym = mname isa Symbol ? mname : (mname isa GlobalRef ? mname.name : nothing)
            sym in (Symbol("@forall"), Symbol("@exists")) && return true
        end
        return any(has_quantifier, e.args)
    end
    return false
end

"""
    generate_smtlib_query(spec::FormalSpecification; logic="") -> String

Generates a complete SMT-LIB 2.6 query file asserting the preconditions and the NEGATION
of the postconditions. If satisfiable (`sat`), a counterexample exists.
"""
function generate_smtlib_query(spec::FormalSpecification; logic::String="")::String
    has_quant = any(has_quantifier, spec.preconditions) || any(has_quantifier, spec.postconditions)
    # Use ALL if structs, quantifiers, or complex sorts are present, otherwise default to QF_LRA
    effective_logic = if !isempty(logic)
        logic
    elseif !isempty(STRUCT_REGISTRY) || has_quant
        "ALL"
    else
        "QF_LRA"
    end

    lines = String[
        "; Generated by JuLean.jl for $(spec.name)",
        "(set-logic $effective_logic)",
        "(set-option :produce-models true)"
    ]

    # Declare algebraic datatypes for any registered structs
    for (sname, sdecl) in STRUCT_REGISTRY
        field_defs = join(["($(f[1]) $(julia_to_smt_type(f[2])))" for f in sdecl.fields], " ")
        push!(lines, "(declare-datatypes () (($sname (mk-$sname $field_defs))))")
    end

    # Declare argument constants
    for arg in spec.args
        t = get(spec.arg_types, arg, Real)
        sort_str = julia_to_smt_type(t)
        push!(lines, "(declare-const $arg $sort_str)")
    end

    # Declare result constant
    ret_sort = julia_to_smt_type(spec.return_type)
    push!(lines, "(declare-const result $ret_sort)")

    # Assert function body equivalence: result = body
    body_smt = julia_to_smt_expr(spec.body)
    push!(lines, "(assert (= result $body_smt))")

    # Assert preconditions
    for (i, pre) in enumerate(spec.preconditions)
        pre_smt = julia_to_smt_expr(pre)
        push!(lines, "; Precondition $i\n(assert $pre_smt)")
    end

    # Formulate conjunction of postconditions
    post_smts = String[]
    for post in spec.postconditions
        push!(post_smts, julia_to_smt_expr(post))
    end

    all_posts = if isempty(post_smts)
        "true"
    elseif length(post_smts) == 1
        post_smts[1]
    else
        "(and " * join(post_smts, " ") * ")"
    end

    # Assert negation of postconditions to search for a counterexample
    push!(lines, "; Specification falsification target (not postconditions)")
    push!(lines, "(assert (not $all_posts))")

    push!(lines, "(check-sat)")
    push!(lines, "(get-model)")

    return join(lines, "\n") * "\n"
end
