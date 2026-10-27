# JuLean.jl - Design-by-Contract & Specification System

using MacroTools

"""
Global toggle for dynamic contract checking.
"""
const CONTRACTS_ENABLED = Ref{Bool}(true)

"""
    enable_contracts!(enabled::Bool=true)

Enable or disable runtime contract checking.
"""
function enable_contracts!(enabled::Bool=true)
    CONTRACTS_ENABLED[] = enabled
    return enabled
end

"""
    disable_contracts!()

Disable runtime contract checking (for zero-overhead production execution).
"""
disable_contracts!() = enable_contracts!(false)

"""
    implies(p::Bool, q::Bool) -> Bool
    p ⟹ q -> Bool
    p --> q -> Bool

Logical implication operator: `p ==> q` is true unless `p` is true and `q` is false.
"""
implies(p::Bool, q::Bool)::Bool = !p || q

# Infix operators for implication
const ⟹ = implies
const --> = implies

# Export operators
export implies, ⟹, -->, @forall, @exists

"""
    @forall(var in collection, condition)
    @forall(var::Type, condition)

Universal quantifier specification.
- For discrete collections or ranges (e.g. `i in 1:n`), evaluates `all(i -> condition, collection)` at runtime.
- For typed domains (e.g. `x::Real`), evaluated symbolically by Lean 4 and SMT solvers.
"""
macro forall(binding, cond)
    if binding isa Expr && binding.head == :call && binding.args[1] in (:in, :∈)
        var = binding.args[2]
        coll = binding.args[3]
        return :(all($(esc(var)) -> $(esc(cond)), $(esc(coll))))
    elseif binding isa Expr && (binding.head == :comparison || binding.head == :in)
        var = binding.args[1]
        coll = binding.args[end]
        return :(all($(esc(var)) -> $(esc(cond)), $(esc(coll))))
    else
        return :(true)
    end
end

"""
    @exists(var in collection, condition)
    @exists(var::Type, condition)

Existential quantifier specification.
- For discrete collections or ranges (e.g. `i in 1:n`), evaluates `any(i -> condition, collection)` at runtime.
- For typed domains (e.g. `x::Real`), evaluated symbolically by Lean 4 and SMT solvers.
"""
macro exists(binding, cond)
    if binding isa Expr && binding.head == :call && binding.args[1] in (:in, :∈)
        var = binding.args[2]
        coll = binding.args[3]
        return :(any($(esc(var)) -> $(esc(cond)), $(esc(coll))))
    elseif binding isa Expr && (binding.head == :comparison || binding.head == :in)
        var = binding.args[1]
        coll = binding.args[end]
        return :(any($(esc(var)) -> $(esc(cond)), $(esc(coll))))
    else
        return :(true)
    end
end

"""
    requires(condition::Bool, msg::AbstractString="")

Runtime check for a precondition. Throws `ContractViolationError` if `condition` is false.
"""
function requires(condition::Bool, msg::AbstractString="", func_name::Symbol=:unknown)
    if CONTRACTS_ENABLED[] && !condition
        throw(ContractViolationError(:precondition, msg, "Precondition violated", func_name))
    end
    return nothing
end

"""
    ensures(condition::Bool, msg::AbstractString="")

Runtime check for a postcondition. Throws `ContractViolationError` if `condition` is false.
"""
function ensures(condition::Bool, msg::AbstractString="", func_name::Symbol=:unknown)
    if CONTRACTS_ENABLED[] && !condition
        throw(ContractViolationError(:postcondition, msg, "Postcondition violated", func_name))
    end
    return nothing
end

"""
    invariant(condition::Bool, msg::AbstractString="")

Runtime check for an invariant. Throws `ContractViolationError` if `condition` is false.
"""
function invariant(condition::Bool, msg::AbstractString="", func_name::Symbol=:unknown)
    if CONTRACTS_ENABLED[] && !condition
        throw(ContractViolationError(:invariant, msg, "Invariant violated", func_name))
    end
    return nothing
end

"""
    @requires condition [message]

Declare a function precondition. Can be used inside `@contract` or `@formalize` functions,
or standalone as a runtime precondition check.
"""
macro requires(cond, msg="")
    msg_str = msg == "" ? string(cond) : msg
    return quote
        if $(@__MODULE__).CONTRACTS_ENABLED[] && !($(esc(cond)))
            throw($(@__MODULE__).ContractViolationError(:precondition, $(string(cond)), $(esc(msg_str)), :block))
        end
    end
end

"""
    @ensures condition [message]

Declare a function postcondition. Can be used inside `@contract` or `@formalize` functions.
Inside postconditions, `result` refers to the return value of the function.
"""
macro ensures(cond, msg="")
    msg_str = msg == "" ? string(cond) : msg
    return quote
        if $(@__MODULE__).CONTRACTS_ENABLED[] && !($(esc(cond)))
            throw($(@__MODULE__).ContractViolationError(:postcondition, $(string(cond)), $(esc(msg_str)), :block))
        end
    end
end

"""
    @invariant condition [message]

Declare a loop or data invariant.
"""
macro invariant(cond, msg="")
    msg_str = msg == "" ? string(cond) : msg
    return quote
        if $(@__MODULE__).CONTRACTS_ENABLED[] && !($(esc(cond)))
            throw($(@__MODULE__).ContractViolationError(:invariant, $(string(cond)), $(esc(msg_str)), :block))
        end
    end
end

"""
    extract_contracts(body::Expr) -> (preconditions, postconditions, invariants, clean_body)

Inspects a function body AST, extracts all `@requires`, `@ensures`, `@invariant` calls,
and returns the separated conditions and the remaining executable body.
"""
function extract_contracts(body::Expr)
    preconditions = Expr[]
    postconditions = Expr[]
    invariants = Expr[]
    clean_stmts = Any[]

    stmts = body.head == :block ? body.args : Any[body]

    for stmt in stmts
        if stmt isa LineNumberNode
            push!(clean_stmts, stmt)
            continue
        end

        extracted = false
        if stmt isa Expr
            # Macro calls: @requires, @ensures, @invariant
            if stmt.head == :macrocall && length(stmt.args) >= 3
                mname = stmt.args[1]
                sym = mname isa Symbol ? mname : (mname isa GlobalRef ? mname.name : nothing)
                if sym == Symbol("@requires")
                    push!(preconditions, stmt.args[3])
                    extracted = true
                elseif sym == Symbol("@ensures")
                    push!(postconditions, stmt.args[3])
                    extracted = true
                elseif sym == Symbol("@invariant")
                    push!(invariants, stmt.args[3])
                    extracted = true
                end
            # Function calls: requires(...), ensures(...), invariant(...)
            elseif stmt.head == :call && length(stmt.args) >= 2
                fn = stmt.args[1]
                sym = fn isa Symbol ? fn : (fn isa GlobalRef ? fn.name : nothing)
                if sym == :requires
                    push!(preconditions, stmt.args[2])
                    extracted = true
                elseif sym == :ensures
                    push!(postconditions, stmt.args[2])
                    extracted = true
                elseif sym == :invariant
                    push!(invariants, stmt.args[2])
                    extracted = true
                end
            end
        end

        if !extracted
            push!(clean_stmts, stmt)
        end
    end

    clean_body = Expr(:block, clean_stmts...)
    return preconditions, postconditions, invariants, clean_body
end

"""
    instrument_contract_body(fn_name::Symbol, pre::Vector{Expr}, post::Vector{Expr}, clean_body::Expr)

Constructs the instrumented Julia AST that checks preconditions before running the body,
captures the return value in `result`, checks postconditions, and returns `result`.
"""
function instrument_contract_body(fn_name::Symbol, pre::Vector{Expr}, post::Vector{Expr}, clean_body::Expr)
    pre_checks = Expr[]
    for p in pre
        p_str = string(p)
        push!(pre_checks, quote
            if $(@__MODULE__).CONTRACTS_ENABLED[] && !($p)
                throw($(@__MODULE__).ContractViolationError(:precondition, $p_str, "Precondition violated", $(QuoteNode(fn_name))))
            end
        end)
    end

    post_checks = Expr[]
    for q in post
        q_str = string(q)
        push!(post_checks, quote
            if $(@__MODULE__).CONTRACTS_ENABLED[] && !($q)
                throw($(@__MODULE__).ContractViolationError(:postcondition, $q_str, "Postcondition violated", $(QuoteNode(fn_name))))
            end
        end)
    end

    return quote
        $(pre_checks...)
        result = $(clean_body)
        $(post_checks...)
        return result
    end
end

"""
    @contract function ... end

Enforces contracts (`@requires`, `@ensures`) on a function at runtime.
"""
macro contract(fdef)
    dict = MacroTools.splitdef(fdef)
    fn_name = dict[:name]
    pre, post, inv, clean_body = extract_contracts(dict[:body])

    dict[:body] = instrument_contract_body(fn_name, pre, post, clean_body)
    return esc(MacroTools.combinedef(dict))
end
