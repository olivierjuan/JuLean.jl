# JuLean.jl - Julia AST to Lean 4 Transpiler

using MacroTools

"""
Global registry for user-defined Julia-to-Lean type mappings.
"""
const CUSTOM_TYPE_REGISTRY = Dict{Any, LeanType}()

"""
Global registry for formalized user structs.
"""
const STRUCT_REGISTRY = Dict{Symbol, LeanStructure}()

"""
    extract_struct_decl(sdef::Expr) -> LeanStructure

Extracts a `LeanStructure` declaration from a Julia struct definition AST.
"""
function extract_struct_decl(sdef::Expr)::LeanStructure
    name_part = sdef.args[2]
    struct_name = name_part isa Symbol ? name_part : (name_part isa Expr ? name_part.args[1] : Symbol(string(name_part)))

    body = sdef.args[3]
    fields = Tuple{String, LeanType}[]

    for stmt in body.args
        if stmt isa LineNumberNode
            continue
        elseif stmt isa Symbol
            push!(fields, (string(stmt), LeanRat()))
        elseif stmt isa Expr && stmt.head == :(::)
            fname = string(stmt.args[1])
            ftype = julia_to_lean_type(stmt.args[2])
            push!(fields, (fname, ftype))
        end
    end

    lean_struct = LeanStructure(string(struct_name), String[], fields, "Julia struct $(struct_name)")
    STRUCT_REGISTRY[struct_name] = lean_struct
    register_lean_type!(struct_name, string(struct_name))
    return lean_struct
end

"""
    register_lean_type!(jl_type, lean_type::LeanType)
    register_lean_type!(jl_type, lean_name::String)

Registers a custom mapping from a Julia type (or Symbol) to a `LeanType`.
Allows domain-specific packages to define their own Lean type bindings.
"""
function register_lean_type!(jl_type, lean_type::LeanType)
    CUSTOM_TYPE_REGISTRY[jl_type] = lean_type
    return lean_type
end

register_lean_type!(jl_type, lean_name::String) = register_lean_type!(jl_type, LeanNamedType(lean_name))

"""
    julia_to_lean_type(jl_type) -> LeanType

Maps a Julia type or type expression to the corresponding `LeanType`.
"""
function julia_to_lean_type(t)::LeanType
    if haskey(CUSTOM_TYPE_REGISTRY, t)
        return CUSTOM_TYPE_REGISTRY[t]
    end

    if t in (:Int, :Int64, :Int32, :Integer, Int, Int64, Int32, Integer)
        return LeanInt()
    elseif t in (:UInt, :UInt64, :UInt32, :Nat, UInt, UInt64)
        return LeanNat()
    elseif t in (:Rational, Rational)
        return LeanRat()
    elseif t in (:Float64, :Float32, :Real, Float64, Float32, Real)
        return LeanRat()
    elseif t in (:Bool, Bool)
        return LeanBool()
    elseif t in (:String, String, :Symbol, Symbol)
        return LeanString()
    elseif t isa Expr && t.head == :curly
        base = t.args[1]
        if base in (:Vector, :Array)
            elem = length(t.args) >= 2 ? julia_to_lean_type(t.args[2]) : LeanRat()
            return LeanArray(elem)
        elseif base in (:Set, :Finset)
            elem = length(t.args) >= 2 ? julia_to_lean_type(t.args[2]) : LeanRat()
            return LeanFinset(elem)
        elseif base == :Rational
            return LeanRat()
        else
            type_args = [julia_to_lean_type(a) for a in t.args[2:end]]
            return LeanNamedType(string(base), type_args)
        end
    elseif t isa Symbol
        return LeanNamedType(string(t))
    end
    return LeanRat() # default fallback for numerical optimization variables
end

"""
Unwraps single-statement blocks and returns, discarding LineNumberNodes.
"""
function unwrap_ast_expr(ex)
    if ex isa Expr && ex.head == :block
        clean_args = filter(a -> !(a isa LineNumberNode), ex.args)
        if isempty(clean_args)
            return true
        elseif length(clean_args) == 1
            return unwrap_ast_expr(clean_args[1])
        end
    elseif ex isa Expr && ex.head == :return
        return isempty(ex.args) ? true : unwrap_ast_expr(ex.args[1])
    end
    return ex
end

"""
    julia_to_lean_expr(expr) -> LeanExpr

Recursively converts a Julia expression or value into a `LeanExpr`.
"""
function julia_to_lean_expr(ex)::LeanExpr
    unwrapped = unwrap_ast_expr(ex)

    if unwrapped isa Integer
        return LeanLitInt(Int(unwrapped))
    elseif unwrapped isa Rational
        return LeanLitRat(BigInt(numerator(unwrapped)), BigInt(denominator(unwrapped)))
    elseif unwrapped isa AbstractFloat
        # Check if float is an exact integer/fraction
        r = rationalize(BigInt, unwrapped)
        if denominator(r) == 1
            return LeanLitRat(numerator(r), 1)
        else
            return LeanLitRat(numerator(r), denominator(r))
        end
    elseif unwrapped isa Bool
        return LeanLitBool(unwrapped)
    elseif unwrapped isa AbstractString
        return LeanLitString(String(unwrapped))
    elseif unwrapped isa Symbol
        return LeanVar(string(unwrapped))
    elseif !(unwrapped isa Expr)
        return LeanRawExpr(string(unwrapped))
    end

    # Expr handling
    e = unwrapped::Expr

    # Ignore LineNumberNodes inside blocks
    if e.head == :block
        clean_args = filter(a -> !(a isa LineNumberNode), e.args)
        if isempty(clean_args)
            return LeanLitBool(true)
        elseif length(clean_args) == 1
            return julia_to_lean_expr(clean_args[1])
        else
            # Translate sequence of let-bindings
            return build_lean_block(clean_args)
        end
    elseif e.head == :return
        return isempty(e.args) ? LeanLitBool(true) : julia_to_lean_expr(e.args[1])
    elseif e.head == :(=) && length(e.args) == 2
        var_name = string(e.args[1])
        val = julia_to_lean_expr(e.args[2])
        return LeanLet(var_name, val, LeanVar(var_name))
    elseif e.head in (:if, :elseif)
        cond = julia_to_lean_expr(e.args[1])
        then_b = julia_to_lean_expr(e.args[2])
        else_b = length(e.args) >= 3 ? julia_to_lean_expr(e.args[3]) : LeanLitBool(true)
        return LeanIf(cond, then_b, else_b)
    elseif e.head == :. && length(e.args) == 2
        obj = julia_to_lean_expr(e.args[1])
        field_sym = e.args[2] isa QuoteNode ? e.args[2].value : e.args[2]
        return LeanFieldAccess(obj, string(field_sym))
    elseif e.head == :ref && length(e.args) >= 2
        coll = julia_to_lean_expr(e.args[1])
        idx = julia_to_lean_expr(e.args[2])
        return LeanIndexAccess(coll, idx)
    elseif e.head == :call
        return translate_call(e.args)
    elseif e.head in (:&&, :and)
        left = julia_to_lean_expr(e.args[1])
        right = julia_to_lean_expr(e.args[2])
        return LeanBinOp(:∧, left, right)
    elseif e.head in (:||, :or)
        left = julia_to_lean_expr(e.args[1])
        right = julia_to_lean_expr(e.args[2])
        return LeanBinOp(:∨, left, right)
    elseif e.head == :comparison
        # Handle chained comparisons like lb <= f <= ub
        return translate_comparison(e.args)
    elseif e.head == Symbol("-->") || e.head == Symbol("⟹")
        left = julia_to_lean_expr(e.args[1])
        right = julia_to_lean_expr(e.args[2])
        return LeanBinOp(:→, left, right)
    elseif e.head == :macrocall
        return translate_lean_macro(e)
    else
        return LeanRawExpr(string(ex))
    end
end

"""
Translates supported macros (like @forall, @exists) into Lean quantifier expressions.
"""
function translate_lean_macro(e::Expr)::LeanExpr
    mname = e.args[1]
    sym = mname isa Symbol ? mname : (mname isa GlobalRef ? mname.name : nothing)
    clean_args = filter(a -> !(a isa LineNumberNode), e.args[2:end])

    if sym in (Symbol("@forall"), Symbol("@exists")) && length(clean_args) >= 2
        binding = clean_args[1]
        cond_expr = julia_to_lean_expr(clean_args[2])
        is_forall = (sym == Symbol("@forall"))

        # Form: i in a:b
        if binding isa Expr && binding.head == :call && binding.args[1] in (:in, :∈) && length(binding.args) == 3
            var_name = string(binding.args[2])
            rng = binding.args[3]
            if rng isa Expr && rng.head == :call && rng.args[1] == :(:) && length(rng.args) == 3
                a_expr = julia_to_lean_expr(rng.args[2])
                b_expr = julia_to_lean_expr(rng.args[3])
                v_expr = LeanVar(var_name)
                bounds = LeanBinOp(:∧, LeanBinOp(:<=, a_expr, v_expr), LeanBinOp(:<=, v_expr, b_expr))
                inner = is_forall ? LeanBinOp(:→, bounds, cond_expr) : LeanBinOp(:∧, bounds, cond_expr)
                return is_forall ? LeanForall(var_name, LeanNat(), inner) : LeanExists(var_name, LeanNat(), inner)
            else
                return is_forall ? LeanForall(var_name, LeanNat(), cond_expr) : LeanExists(var_name, LeanNat(), cond_expr)
            end
        elseif binding isa Expr && binding.head == :(::)
            var_name = string(binding.args[1])
            var_type = julia_to_lean_type(binding.args[2])
            return is_forall ? LeanForall(var_name, var_type, cond_expr) : LeanExists(var_name, var_type, cond_expr)
        elseif binding isa Symbol
            var_name = string(binding)
            return is_forall ? LeanForall(var_name, LeanRat(), cond_expr) : LeanExists(var_name, LeanRat(), cond_expr)
        end
    end

    return LeanRawExpr(string(e))
end

"""
Translate a block of Julia statements into nested Lean `let` bindings.
"""
function build_lean_block(stmts::Vector{Any})::LeanExpr
    if isempty(stmts)
        return LeanLitBool(true)
    end
    stmt = stmts[1]
    rest = stmts[2:end]

    if stmt isa Expr && stmt.head == :(=) && length(stmt.args) == 2
        var_name = string(stmt.args[1])
        val = julia_to_lean_expr(stmt.args[2])
        body = isempty(rest) ? LeanVar(var_name) : build_lean_block(rest)
        return LeanLet(var_name, val, body)
    elseif stmt isa Expr && stmt.head == :return
        return julia_to_lean_expr(stmt.args[1])
    else
        expr_curr = julia_to_lean_expr(stmt)
        if isempty(rest)
            return expr_curr
        else
            return build_lean_block(rest)
        end
    end
end

"""
Translate Julia function calls and binary operators.
"""
function translate_call(args::Vector{Any})::LeanExpr
    fn = args[1]
    fn_sym = fn isa Symbol ? fn : (fn isa GlobalRef ? fn.name : nothing)

    # Infix operators
    if fn_sym in (:+, :-, :*, :/, :(==), :!=, :<, :<=, :>, :>=, :≤, :≥, :≠)
        if length(args) == 3
            left = julia_to_lean_expr(args[2])
            right = julia_to_lean_expr(args[3])
            return LeanBinOp(fn_sym, left, right)
        elseif length(args) == 2 && fn_sym == :-
            return LeanUnaryOp(:-, julia_to_lean_expr(args[2]))
        end
    elseif fn_sym in (:!, :¬)
        return LeanUnaryOp(:¬, julia_to_lean_expr(args[2]))
    elseif fn_sym in (:implies, :⟹, Symbol("-->"))
        left = julia_to_lean_expr(args[2])
        right = julia_to_lean_expr(args[3])
        return LeanBinOp(:→, left, right)
    elseif fn_sym in (:&&, :and)
        left = julia_to_lean_expr(args[2])
        right = julia_to_lean_expr(args[3])
        return LeanBinOp(:∧, left, right)
    elseif fn_sym in (:||, :or)
        left = julia_to_lean_expr(args[2])
        right = julia_to_lean_expr(args[3])
        return LeanBinOp(:∨, left, right)
    end

    # Standard function application
    if fn_sym !== nothing && haskey(STRUCT_REGISTRY, fn_sym)
        return LeanApp(LeanVar("$(fn_sym).mk"), [julia_to_lean_expr(a) for a in args[2:end]])
    elseif fn_sym in (:length, :size) && length(args) == 2
        return LeanFieldAccess(julia_to_lean_expr(args[2]), "size")
    end

    lean_fn = julia_to_lean_expr(fn)
    lean_args = [julia_to_lean_expr(a) for a in args[2:end]]
    return LeanApp(lean_fn, lean_args)
end

"""
Translate chained comparison expressions (e.g. `a <= b <= c` -> `a ≤ b ∧ b ≤ c`).
"""
function translate_comparison(args::Vector{Any})::LeanExpr
    # args has form [a, op1, b, op2, c, ...]
    terms = LeanExpr[]
    for i in 2:2:length(args)
        op = args[i]
        l = julia_to_lean_expr(args[i-1])
        r = julia_to_lean_expr(args[i+1])
        push!(terms, LeanBinOp(op, l, r))
    end
    if length(terms) == 1
        return terms[1]
    else
        res = terms[1]
        for t in terms[2:end]
            res = LeanBinOp(:∧, res, t)
        end
        return res
    end
end

"""
    substitute_var(e::LeanExpr, old_name::String, replacement::LeanExpr) -> LeanExpr

Replaces occurrences of `LeanVar(old_name)` with `replacement` in `e`.
"""
function substitute_var(e::LeanExpr, old_name::String, replacement::LeanExpr)::LeanExpr
    if e isa LeanVar
        return e.name == old_name ? replacement : e
    elseif e isa LeanApp
        new_fn = substitute_var(e.fn, old_name, replacement)
        new_args = [substitute_var(a, old_name, replacement) for a in e.args]
        return LeanApp(new_fn, new_args)
    elseif e isa LeanBinOp
        return LeanBinOp(e.op, substitute_var(e.left, old_name, replacement), substitute_var(e.right, old_name, replacement))
    elseif e isa LeanUnaryOp
        return LeanUnaryOp(e.op, substitute_var(e.arg, old_name, replacement))
    elseif e isa LeanIf
        return LeanIf(substitute_var(e.cond, old_name, replacement),
                      substitute_var(e.then_expr, old_name, replacement),
                      substitute_var(e.else_expr, old_name, replacement))
    elseif e isa LeanLet
        if e.var == old_name
            return LeanLet(e.var, substitute_var(e.val, old_name, replacement), e.body)
        else
            return LeanLet(e.var, substitute_var(e.val, old_name, replacement), substitute_var(e.body, old_name, replacement))
        end
    elseif e isa LeanFieldAccess
        return LeanFieldAccess(substitute_var(e.obj, old_name, replacement), e.field)
    elseif e isa LeanIndexAccess
        return LeanIndexAccess(substitute_var(e.collection, old_name, replacement), substitute_var(e.index, old_name, replacement))
    elseif e isa LeanForall
        return e.var == old_name ? e : LeanForall(e.var, e.type, substitute_var(e.body, old_name, replacement))
    elseif e isa LeanExists
        return e.var == old_name ? e : LeanExists(e.var, e.type, substitute_var(e.body, old_name, replacement))
    else
        return e
    end
end

"""
    transpile_to_lean_decl(spec::FormalSpecification; tactic="") -> (LeanDef, LeanTheorem)

Generates both the Lean 4 `def` and the verification `theorem` from a `FormalSpecification`.
"""
function transpile_to_lean_decl(spec::FormalSpecification; tactic::String="")
    fn_name = string(spec.name)
    lean_args = Tuple{String, LeanType}[]
    for a in spec.args
        t = get(spec.arg_types, a, LeanRat())
        lt = t isa LeanType ? t : julia_to_lean_type(t)
        push!(lean_args, (string(a), lt))
    end

    ret_type = spec.return_type isa LeanType ? spec.return_type : julia_to_lean_type(spec.return_type)
    lean_body = julia_to_lean_expr(spec.body)

    lean_def = LeanDef(fn_name, lean_args, ret_type, lean_body, spec.docstring)

    # Verification theorem
    thm_name = "$(fn_name)_spec"
    hyps = Tuple{String, LeanExpr}[]
    for (i, pre) in enumerate(spec.preconditions)
        push!(hyps, ("h_pre_$i", julia_to_lean_expr(pre)))
    end

    # Postconditions with `result` replaced by call to the defined function
    call_expr = LeanApp(LeanVar(fn_name), [LeanVar(string(a)) for a in spec.args])
    post_exprs = LeanExpr[]
    for post in spec.postconditions
        post_lean = julia_to_lean_expr(post)
        substituted = substitute_var(post_lean, "result", call_expr)
        push!(post_exprs, substituted)
    end

    stmt = if isempty(post_exprs)
        LeanBinOp(:(==), call_expr, call_expr)
    elseif length(post_exprs) == 1
        post_exprs[1]
    else
        res = post_exprs[1]
        for p in post_exprs[2:end]
            res = LeanBinOp(:∧, res, p)
        end
        res
    end

    default_tactic = if isempty(tactic)
        synthesize_tactic(spec)
    else
        tactic
    end

    lean_thm = LeanTheorem(thm_name, lean_args, hyps, stmt, default_tactic, "Specification for `$(fn_name)`")

    return lean_def, lean_thm
end

"""
    has_branching(ex) -> Bool

Checks whether an AST contains conditional expressions (if, elseif).
"""
function has_branching(ex)::Bool
    if ex isa Expr
        if ex.head in (:if, :elseif)
            return true
        end
        return any(has_branching, ex.args)
    end
    return false
end

"""
    synthesize_tactic(spec::FormalSpecification) -> String

Generates an automated, intelligent Lean 4 tactic script matching the specification shape:
- If quantifiers are present: introduces variables (`intros`).
- If branching (`if` / `elseif`) is present: splits conditionals (`split_ifs`) and solves branches.
- Solves goals via `linarith`, `omega`, `decide`, or `rfl`.
"""
function synthesize_tactic(spec::FormalSpecification)::String
    lines = String["by", "  unfold $(spec.name)"]

    has_branch = has_branching(spec.body)
    has_quant = any(e -> (e isa Expr && (e.head == :macrocall || occursin("forall", string(e)))), spec.postconditions)

    if has_quant
        push!(lines, "  try (intros)")
    end

    if has_branch
        push!(lines, "  try (split_ifs <;> try constructor <;> try linarith <;> try omega <;> try decide <;> try rfl)")
    end

    push!(lines, "  first | linarith | omega | decide | rfl | aesop | norm_num")
    return join(lines, "\n")
end
