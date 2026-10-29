# JuLean.jl - Julia AST to Lean 4 Transpiler

using MacroTools

"""
Global registry for user-defined Julia-to-Lean type mappings.
"""
const CUSTOM_TYPE_REGISTRY = Dict{Any, LeanType}(
    :PosInt => LeanPNat(),
    :NodeId => LeanPNat(),
    :ArcId => LeanPNat(),
    :PNat => LeanPNat(),
    Symbol("ℕ+") => LeanPNat(),
    PosInt => LeanPNat()
)

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

    if t isa Expr && t.head == :. && length(t.args) == 2
        sym = t.args[2] isa QuoteNode ? t.args[2].value : t.args[2]
        return julia_to_lean_type(sym)
    end

    if t in (:PNat, :PosInt, :NodeId, :ArcId, :PositiveInt, Symbol("ℕ+"), PNat, PosInt)
        return LeanPNat()
    elseif t in (:Int, :Int64, :Int32, :Integer, Int, Int64, Int32, Integer)
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
    is_pnat_type(t) -> Bool

Checks if a Julia or Lean type represents a strictly positive integer (`ℕ+` / `PNat`).
"""
function is_pnat_type(t)::Bool
    t === nothing && return false
    if t isa Expr && t.head == :. && length(t.args) == 2
        sym = t.args[2] isa QuoteNode ? t.args[2].value : t.args[2]
        return is_pnat_type(sym)
    end
    return t in (:PNat, :PosInt, :NodeId, :ArcId, :PositiveInt, Symbol("ℕ+"), PNat, PosInt, LeanPNat()) || (t isa LeanPNat)
end

"""
    translate_1based_index(raw_idx, fn_args, loop_vars, fn_arg_types) -> LeanExpr

Translates a 1-based Julia index expression into a 0-based Lean 4 index:
- Loop variable `i` (already 0-based in Lean 4): `i`
- Loop variable offset `i + k`: `i + k`
- Positive integer / PNat `p`: `p.1 - 1` (pure Nat arithmetic without any .toNat cast!)
- Integer literal `k`: `k - 1` (statically converted at transpile-time)
- General `Int` expression `x`: `(x - 1).toNat`
"""
function translate_1based_index(raw_idx, fn_args::Vector{String}=String[], loop_vars::Set{String}=Set{String}(), fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::LeanExpr
    if raw_idx isa Symbol && string(raw_idx) in loop_vars
        return LeanVar(string(raw_idx))
    elseif raw_idx isa Symbol && (get(fn_arg_types, raw_idx, nothing) in (:UInt, :UInt64, :UInt32, :Nat, UInt, UInt64, LeanNat()))
        return LeanVar(string(raw_idx))
    elseif raw_idx isa Symbol && is_pnat_type(get(fn_arg_types, raw_idx, nothing))
        return LeanRawExpr("($(string(raw_idx)).1 - 1)")
    elseif raw_idx isa Expr && raw_idx.head == :call && length(raw_idx.args) == 3 && raw_idx.args[1] == :+ &&
           (raw_idx.args[2] isa Symbol && string(raw_idx.args[2]) in loop_vars)
        offset = raw_idx.args[3]
        return LeanBinOp(:+, LeanVar(string(raw_idx.args[2])), julia_to_lean_expr(offset, fn_args, loop_vars, fn_arg_types))
    elseif raw_idx isa Integer
        return raw_idx == 0 ? LeanLitInt(0) : LeanLitInt(Int(raw_idx) - 1)
    else
        idx_inner = to_lean(julia_to_lean_expr(raw_idx, fn_args, loop_vars, fn_arg_types))
        return LeanRawExpr("($idx_inner - 1).toNat")
    end
end

"""
Recursively converts a Julia expression or value into a `LeanExpr`.
"""
function julia_to_lean_expr(ex, fn_args::Vector{String}=String[], loop_vars::Set{String}=Set{String}(), fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::LeanExpr
    unwrapped = unwrap_ast_expr(ex)

    if unwrapped isa Bool
        return LeanLitBool(unwrapped)
    elseif unwrapped isa Integer
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
            return julia_to_lean_expr(clean_args[1], fn_args, loop_vars, fn_arg_types)
        elseif is_imperative_block(clean_args)
            return LeanIdRun(build_imperative_do_block(clean_args, fn_args, fn_arg_types))
        else
            # Translate sequence of let-bindings
            return build_lean_block(clean_args)
        end
    elseif e.head == :vect
        clean_args = filter(a -> !(a isa LineNumberNode), e.args)
        return LeanArrayLit([julia_to_lean_expr(a, fn_args, loop_vars, fn_arg_types) for a in clean_args])
    elseif e.head == :return
        return isempty(e.args) ? LeanLitBool(true) : julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
    elseif e.head == :(=) && length(e.args) == 2
        var_name = string(e.args[1])
        val = julia_to_lean_expr(e.args[2], fn_args, loop_vars, fn_arg_types)
        return LeanLet(var_name, val, LeanVar(var_name))
    elseif e.head in (:if, :elseif)
        cond = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        then_b = julia_to_lean_expr(e.args[2], fn_args, loop_vars, fn_arg_types)
        else_b = length(e.args) >= 3 ? julia_to_lean_expr(e.args[3], fn_args, loop_vars, fn_arg_types) : LeanLitBool(true)
        return LeanIf(cond, then_b, else_b)
    elseif e.head == :. && length(e.args) == 2
        obj = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        field_sym = e.args[2] isa QuoteNode ? e.args[2].value : e.args[2]
        return LeanFieldAccess(obj, string(field_sym))
    elseif e.head == :ref && length(e.args) == 1
        # Empty array constructor like Int[] or Float64[]
        return LeanArrayLit(LeanExpr[])
    elseif e.head == :ref && length(e.args) >= 2
        coll = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        raw_idx = e.args[2]
        idx = translate_1based_index(raw_idx, fn_args, loop_vars, fn_arg_types)
        return LeanIndexAccess(coll, idx)
    elseif e.head == :call
        return translate_call(e.args, fn_args, loop_vars, fn_arg_types)
    elseif e.head in (:&&, :and)
        left = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(e.args[2], fn_args, loop_vars, fn_arg_types)
        return LeanBinOp(:∧, left, right)
    elseif e.head in (:||, :or)
        left = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(e.args[2], fn_args, loop_vars, fn_arg_types)
        return LeanBinOp(:∨, left, right)
    elseif e.head == :comparison
        # Handle chained comparisons like lb <= f <= ub
        return translate_comparison(e.args, fn_args, loop_vars, fn_arg_types)
    elseif e.head == Symbol("-->") || e.head == Symbol("⟹")
        left = julia_to_lean_expr(e.args[1], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(e.args[2], fn_args, loop_vars, fn_arg_types)
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
    is_imperative_block(stmts::Vector{Any}) -> Bool

Detects whether a list of statements requires imperative Lean 4 `do` execution:
contains loops (`for`, `while`), array mutations (`a[i] = v`, `a[i] += v`),
in-place mutations (`x += v`), or variable reassignments.
"""
function is_imperative_block(stmts::Vector{Any})::Bool
    assigned = Set{Symbol}()
    for s in stmts
        if s isa Expr
            if s.head in (:for, :while)
                return true
            elseif s.head in (:(+=), :(-=), :(*=), :(/=))
                return true
            elseif s.head == :call && length(s.args) >= 2 && s.args[1] in (:push!, :push, :pop!)
                return true
            elseif s.head == :(=) && length(s.args) >= 1 && s.args[1] isa Expr && s.args[1].head == :ref
                return true # a[i] = v
            elseif s.head == :(=) && length(s.args) >= 1 && s.args[1] isa Symbol
                sym = s.args[1]
                if sym in assigned
                    return true # re-assigned variable
                end
                push!(assigned, sym)
            end
        end
    end
    return false
end

function collect_mutated_vars!(mutated::Set{String}, ex)
    if ex isa Expr
        if ex.head in (:(=), :(+=), :(-=), :(*=), :(/=)) && length(ex.args) >= 1
            lhs = ex.args[1]
            if lhs isa Expr && lhs.head == :ref
                push!(mutated, string(lhs.args[1]))
            elseif lhs isa Symbol
                push!(mutated, string(lhs))
            end
        elseif ex.head == :call && length(ex.args) >= 2 && ex.args[1] in (:push!, :push, :pop!)
            push!(mutated, string(ex.args[2]))
        end
        for a in ex.args
            collect_mutated_vars!(mutated, a)
        end
    end
end

"""
    build_imperative_do_block(stmts::Vector{Any}, fn_args::Vector{String}=String[], fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}()) -> LeanDoBlock

Translates an imperative sequence of Julia statements into a `LeanDoBlock`
containing `LeanDoStmt`s and an ending return value.
"""
function build_imperative_do_block(stmts::Vector{Any}, fn_args::Vector{String}=String[], fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::LeanDoBlock
    declared_muts = Set{String}()
    loop_vars = Set{String}()
    do_stmts = LeanDoStmt[]
    ret_expr = LeanLitBool(true)

    mutated = Set{String}()
    for s in stmts
        collect_mutated_vars!(mutated, s)
    end

    # Automatically declare function arguments that are mutated as mutable in Lean 4
    for arg in fn_args
        if arg in mutated
            push!(declared_muts, arg)
            push!(do_stmts, LeanDoLetMut(arg, LeanVar(arg)))
        end
    end

    for (idx, s) in enumerate(stmts)
        # If last statement is a return or an expression
        if idx == length(stmts)
            if s isa Expr && s.head == :return
                ret_expr = isempty(s.args) ? LeanLitBool(true) : julia_to_lean_expr(s.args[1], fn_args, loop_vars, fn_arg_types)
                break
            elseif !(s isa Expr && s.head in (:(=), :(+=), :(-=), :(*=), :(/=), :for, :while))
                # Expression as implicit return
                ret_expr = julia_to_lean_expr(s, fn_args, loop_vars, fn_arg_types)
                break
            end
        end

        st = translate_do_stmt(s, declared_muts, loop_vars, fn_arg_types)
        if st !== nothing
            if st isa LeanDoReturn
                ret_expr = st.expr
                break
            else
                push!(do_stmts, st)
            end
        end
    end

    return LeanDoBlock(do_stmts, ret_expr)
end

function translate_do_body(body_expr, declared_muts::Set{String}, loop_vars::Set{String}, fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::Vector{LeanDoStmt}
    res = LeanDoStmt[]
    stmts = if body_expr isa Expr && body_expr.head == :block
        filter(a -> !(a isa LineNumberNode), body_expr.args)
    else
        [body_expr]
    end

    for s in stmts
        st = translate_do_stmt(s, declared_muts, loop_vars, fn_arg_types)
        if st !== nothing
            push!(res, st)
        end
    end
    return res
end

function translate_do_stmt(stmt, declared_muts::Set{String}, loop_vars::Set{String}, fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::Union{LeanDoStmt, Nothing}
    stmt isa LineNumberNode && return nothing

    # Return
    if stmt isa Expr && stmt.head == :return
        val = isempty(stmt.args) ? LeanLitBool(true) : julia_to_lean_expr(stmt.args[1], String[], loop_vars, fn_arg_types)
        return LeanDoReturn(val)
    end

    # push!(coll, val) -> coll := coll.push val
    if stmt isa Expr && stmt.head == :call && length(stmt.args) >= 3 && stmt.args[1] in (:push!, :push)
        coll_name = string(stmt.args[2])
        val = julia_to_lean_expr(stmt.args[3], String[], loop_vars, fn_arg_types)
        new_val = LeanApp(LeanFieldAccess(LeanVar(coll_name), "push"), [val])
        return LeanDoAssign(coll_name, new_val)
    end

    # Array assignment: arr[idx] = val
    if stmt isa Expr && stmt.head == :(=) && length(stmt.args) == 2 && stmt.args[1] isa Expr && stmt.args[1].head == :ref
        arr_name = string(stmt.args[1].args[1])
        raw_idx = stmt.args[1].args[2]
        idx_expr = translate_1based_index(raw_idx, String[], loop_vars, fn_arg_types)
        val = julia_to_lean_expr(stmt.args[2], String[], loop_vars, fn_arg_types)
        return LeanDoArraySet(arr_name, idx_expr, val)
    end

    # Array compound in-place addition: arr[idx] += val
    if stmt isa Expr && stmt.head == :(+=) && length(stmt.args) == 2 && stmt.args[1] isa Expr && stmt.args[1].head == :ref
        arr_name = string(stmt.args[1].args[1])
        raw_idx = stmt.args[1].args[2]
        idx_expr = translate_1based_index(raw_idx, String[], loop_vars, fn_arg_types)
        old_val = LeanIndexAccess(LeanVar(arr_name), idx_expr)
        new_val = LeanBinOp(:+, old_val, julia_to_lean_expr(stmt.args[2], String[], loop_vars, fn_arg_types))
        return LeanDoArraySet(arr_name, idx_expr, new_val)
    end

    # Scalar in-place compound assignment: x += val
    if stmt isa Expr && stmt.head in (:(+=), :(-=), :(*=), :(/=)) && length(stmt.args) == 2 && stmt.args[1] isa Symbol
        v_name = string(stmt.args[1])
        op = Symbol(string(stmt.head)[1])
        old_val = LeanVar(v_name)
        new_val = LeanBinOp(op, old_val, julia_to_lean_expr(stmt.args[2], String[], loop_vars, fn_arg_types))
        if v_name in declared_muts
            return LeanDoAssign(v_name, new_val)
        else
            push!(declared_muts, v_name)
            return LeanDoLetMut(v_name, new_val)
        end
    end

    # Scalar variable assignment: v = val
    if stmt isa Expr && stmt.head == :(=) && length(stmt.args) == 2 && stmt.args[1] isa Symbol
        v_name = string(stmt.args[1])
        val = julia_to_lean_expr(stmt.args[2], String[], loop_vars, fn_arg_types)

        # Track element type if reading from an array
        if stmt.args[2] isa Expr && stmt.args[2].head == :ref && length(stmt.args[2].args) >= 2
            arr_sym = stmt.args[2].args[1]
            if arr_sym isa Symbol && haskey(fn_arg_types, arr_sym)
                atyp = fn_arg_types[arr_sym]
                if atyp isa LeanArray && is_pnat_type(atyp.elem_type)
                    fn_arg_types[Symbol(v_name)] = :PNat
                elseif atyp isa Expr && atyp.head == :curly && atyp.args[1] in (:Vector, :Array)
                    elem_t = atyp.args[2]
                    if is_pnat_type(elem_t)
                        fn_arg_types[Symbol(v_name)] = :PNat
                    end
                end
            end
        end

        if v_name in declared_muts
            return LeanDoAssign(v_name, val)
        else
            push!(declared_muts, v_name)
            return LeanDoLetMut(v_name, val)
        end
    end

    # For loop: for i in range ... end
    if stmt isa Expr && stmt.head == :for && length(stmt.args) == 2
        iter_spec = stmt.args[1]
        body_expr = stmt.args[2]

        if iter_spec isa Expr && iter_spec.head == :(=) && length(iter_spec.args) == 2
            var_name = string(iter_spec.args[1])
            rng = iter_spec.args[2]

            if rng isa Expr && rng.head == :call && rng.args[1] == :(:) && length(rng.args) == 3
                start_val = rng.args[2]
                stop_val = rng.args[3]
                if start_val == 1
                    new_loop_vars = copy(loop_vars)
                    push!(new_loop_vars, var_name)
                    b_stmts = translate_do_body(body_expr, copy(declared_muts), new_loop_vars, fn_arg_types)
                    return LeanDoForRange(var_name, LeanLitInt(0), julia_to_lean_expr(stop_val, String[], loop_vars, fn_arg_types), b_stmts)
                else
                    new_loop_vars = copy(loop_vars)
                    b_stmts = translate_do_body(body_expr, copy(declared_muts), new_loop_vars, fn_arg_types)
                    return LeanDoForRange(var_name, julia_to_lean_expr(start_val, String[], loop_vars, fn_arg_types), julia_to_lean_expr(stop_val, String[], loop_vars, fn_arg_types), b_stmts)
                end
            else
                coll_expr = julia_to_lean_expr(rng, String[], loop_vars, fn_arg_types)
                b_stmts = translate_do_body(body_expr, copy(declared_muts), loop_vars, fn_arg_types)
                return LeanDoForIn(var_name, coll_expr, b_stmts)
            end
        end
    end

    # While loop: while cond ... end
    if stmt isa Expr && stmt.head == :while && length(stmt.args) == 2
        cond = julia_to_lean_expr(stmt.args[1], String[], loop_vars, fn_arg_types)
        b_stmts = translate_do_body(stmt.args[2], copy(declared_muts), loop_vars, fn_arg_types)
        return LeanDoWhile(cond, b_stmts)
    end

    # If inside do-block
    if stmt isa Expr && stmt.head in (:if, :elseif) && length(stmt.args) >= 2
        cond = julia_to_lean_expr(stmt.args[1], String[], loop_vars, fn_arg_types)
        then_stmts = translate_do_body(stmt.args[2], copy(declared_muts), loop_vars, fn_arg_types)
        else_stmts = length(stmt.args) >= 3 ? translate_do_body(stmt.args[3], copy(declared_muts), loop_vars, fn_arg_types) : LeanDoStmt[]
        return LeanDoIf(cond, then_stmts, else_stmts)
    end

    return LeanDoExpr(julia_to_lean_expr(stmt, String[], loop_vars, fn_arg_types))
end

"""
Translate Julia function calls and binary operators.
"""
function translate_call(args::Vector{Any}, fn_args::Vector{String}=String[], loop_vars::Set{String}=Set{String}(), fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::LeanExpr
    fn = args[1]
    fn_sym = fn isa Symbol ? fn : (fn isa GlobalRef ? fn.name : nothing)

    # Infix operators
    if fn_sym in (:+, :-, :*, :/, :(==), :!=, :<, :<=, :>, :>=, :≤, :≥, :≠)
        if length(args) == 3
            left = julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types)
            right = julia_to_lean_expr(args[3], fn_args, loop_vars, fn_arg_types)
            return LeanBinOp(fn_sym, left, right)
        elseif length(args) == 2 && fn_sym == :-
            return LeanUnaryOp(:-, julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types))
        end
    elseif fn_sym in (:!, :¬)
        return LeanUnaryOp(:¬, julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types))
    elseif fn_sym in (:implies, :⟹, Symbol("-->"))
        left = julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(args[3], fn_args, loop_vars, fn_arg_types)
        return LeanBinOp(:→, left, right)
    elseif fn_sym in (:&&, :and)
        left = julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(args[3], fn_args, loop_vars, fn_arg_types)
        return LeanBinOp(:∧, left, right)
    elseif fn_sym in (:||, :or)
        left = julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types)
        right = julia_to_lean_expr(args[3], fn_args, loop_vars, fn_arg_types)
        return LeanBinOp(:∨, left, right)
    end

    # Standard function application
    if fn_sym !== nothing && haskey(STRUCT_REGISTRY, fn_sym)
        return LeanApp(LeanVar("$(fn_sym).mk"), [julia_to_lean_expr(a, fn_args, loop_vars, fn_arg_types) for a in args[2:end]])
    elseif fn_sym in (:length, :size) && length(args) == 2
        return LeanFieldAccess(julia_to_lean_expr(args[2], fn_args, loop_vars, fn_arg_types), "size")
    end

    lean_fn = julia_to_lean_expr(fn, fn_args, loop_vars, fn_arg_types)
    lean_args = [julia_to_lean_expr(a, fn_args, loop_vars, fn_arg_types) for a in args[2:end]]
    return LeanApp(lean_fn, lean_args)
end

"""
Translate chained comparison expressions (e.g. `a <= b <= c` -> `a ≤ b ∧ b ≤ c`).
"""
function translate_comparison(args::Vector{Any}, fn_args::Vector{String}=String[], loop_vars::Set{String}=Set{String}(), fn_arg_types::Dict{Symbol, Any}=Dict{Symbol, Any}())::LeanExpr
    # args has form [a, op1, b, op2, c, ...]
    terms = LeanExpr[]
    for i in 2:2:length(args)
        op = args[i]
        l = julia_to_lean_expr(args[i-1], fn_args, loop_vars, fn_arg_types)
        r = julia_to_lean_expr(args[i+1], fn_args, loop_vars, fn_arg_types)
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
    elseif e isa LeanArrayLit
        return LeanArrayLit([substitute_var(el, old_name, replacement) for el in e.elements])
    elseif e isa LeanIdRun
        return e
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
    fn_args = [string(a) for a in spec.args]
    lean_body = julia_to_lean_expr(spec.body, fn_args, Set{String}(), spec.arg_types)

    lean_def = LeanDef(fn_name, lean_args, ret_type, lean_body, spec.docstring)

    # Verification theorem
    thm_name = "$(fn_name)_spec"
    hyps = Tuple{String, LeanExpr}[]
    for (i, pre) in enumerate(spec.preconditions)
        push!(hyps, ("h_pre_$i", julia_to_lean_expr(pre, fn_args, Set{String}(), spec.arg_types)))
    end

    # Postconditions with `result` replaced by call to the defined function
    call_expr = LeanApp(LeanVar(fn_name), [LeanVar(string(a)) for a in spec.args])
    post_exprs = LeanExpr[]
    for post in spec.postconditions
        post_lean = julia_to_lean_expr(post, fn_args, Set{String}(), spec.arg_types)
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
