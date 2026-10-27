# JuLean.jl - Julia AST to Lean 4 Transpiler

using MacroTools

"""
    julia_to_lean_type(jl_type) -> LeanType

Maps a Julia type or type expression to the corresponding `LeanType`.
"""
function julia_to_lean_type(t)::LeanType
    if t in (:Int, :Int64, :Int32, :Integer, Int, Int64, Int32, Integer)
        return LeanInt()
    elseif t in (:UInt, :UInt64, :UInt32, :Nat, UInt, UInt64)
        return LeanNat()
    elseif t in (:Rational, :Rational{BigInt}, :Rational{Int}, :Rational{Int64}, Rational, Rational{BigInt})
        return LeanRat()
    elseif t in (:Float64, :Float32, :Real, Float64, Float32, Real)
        # For formal verification of optimization problems (e.g. Dunes/Sirocco exact certificates),
        # Real/Rational are represented as exact ℚ
        return LeanRat()
    elseif t in (:Bool, Bool)
        return LeanBool()
    elseif t in (:String, String)
        return LeanString()
    elseif t in (:Symbol, Symbol)
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
        end
    elseif t isa Symbol
        s = string(t)
        if s in ("ArcStatus", "ComponentType", "PricingRule", "SolverStatus")
            return LeanNamedType(s)
        elseif s in ("GMCFProblem", "Network")
            return LeanNamedType("Network")
        elseif s in ("RationalCertificate", "OptimalityCertificate")
            return LeanNamedType("OptimalityCertificate")
        else
            return LeanNamedType(s)
        end
    end
    return LeanRat() # default fallback for numerical optimization variables
end

"""
    julia_to_lean_expr(expr) -> LeanExpr

Recursively converts a Julia expression or value into a `LeanExpr`.
"""
function julia_to_lean_expr(ex)::LeanExpr
    if ex isa Integer
        return LeanLitInt(Int(ex))
    elseif ex isa Rational
        return LeanLitRat(BigInt(numerator(ex)), BigInt(denominator(ex)))
    elseif ex isa AbstractFloat
        # Check if float is an exact integer/fraction
        r = rationalize(BigInt, ex)
        if denominator(r) == 1
            return LeanLitRat(numerator(r), 1)
        else
            return LeanLitRat(numerator(r), denominator(r))
        end
    elseif ex isa Bool
        return LeanLitBool(ex)
    elseif ex isa AbstractString
        return LeanLitString(String(ex))
    elseif ex isa Symbol
        return LeanVar(string(ex))
    elseif !(ex isa Expr)
        return LeanRawExpr(string(ex))
    end

    # Expr handling
    e = ex::Expr

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
    elseif e.head == :if
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
    else
        return LeanRawExpr(string(ex))
    end
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
        "by\n  unfold $(fn_name)\n  first | linarith | omega | decide | rfl | sorry"
    else
        tactic
    end

    lean_thm = LeanTheorem(thm_name, lean_args, hyps, stmt, default_tactic, "Specification for `$(fn_name)`")

    return lean_def, lean_thm
end
