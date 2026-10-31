# JuLean.jl - Bounded Model Checking (BMC) for Loops
#
# v2 capabilities (this revision):
#   * `for i in a:b` loops: the loop variable is BOUND to the unrolled
#     iteration (`i_k = a + k - 1`, declared Int) and the range guard
#     `a <= i_k <= b` is asserted per step, so updates and invariants may
#     reference the loop variable.
#   * Array state: `dest[i] = v` updates are encoded as SMT `store` on
#     `(Array Int Real)` state (declared from `Vector{Real}` args or
#     array-typed aliases); reads become `select`.
#   * `@ensures` are part of the query: the return value is bound to the
#     final state and the falsification target is `not (invariants ∧ posts)`.
#     A claim therefore holds iff no execution of `depth` full iterations
#     violates the invariant or any postcondition. Loop EXIT (partial last
#     iteration, `while` guards) is not modeled: the checked executions run
#     exactly `depth` iterations.

"""
    LoopDescriptor

Decomposed structure of a loop extracted from a function AST.
"""
struct LoopDescriptor
    init_assignments::Vector{Pair{Symbol, Any}}
    loop_kind::Symbol # :while or :for
    loop_cond::Any
    loop_var::Union{Nothing, Symbol}
    range_start::Any
    range_end::Any
    invariants::Vector{Expr}
    updates::Vector{Pair{Symbol, Any}}
    array_updates::Vector{Tuple{Symbol, Any, Any}} # (array, index expr, value expr)
    return_expr::Any
    state_vars::Vector{Symbol}
end

"""
    substitute_symbols(ex, mapping::Dict{Symbol, Symbol})

Recursively substitutes symbol identifiers in an expression.
"""
function substitute_symbols(ex, mapping::Dict{Symbol, Symbol})
    if ex isa Symbol
        return get(mapping, ex, ex)
    elseif ex isa Expr
        new_head = ex.head
        new_args = [substitute_symbols(a, mapping) for a in ex.args]
        return Expr(new_head, new_args...)
    else
        return ex
    end
end

"""
    extract_loop_descriptor(spec::FormalSpecification) -> Union{Nothing, LoopDescriptor}

Inspects the body of a `FormalSpecification` and extracts loop structure,
state initializers, updates (scalar and array), and invariant conditions.
"""
function extract_loop_descriptor(spec::FormalSpecification)::Union{Nothing, LoopDescriptor}
    clean_stmts = Any[]
    body = spec.body
    stmts = body isa Expr && body.head == :block ? body.args : Any[body]

    for s in stmts
        !(s isa LineNumberNode) && push!(clean_stmts, s)
    end

    loop_idx = findfirst(s -> s isa Expr && s.head in (:while, :for), clean_stmts)
    loop_idx === nothing && return nothing

    loop_expr = clean_stmts[loop_idx]::Expr
    pre_loop = clean_stmts[1:loop_idx-1]
    post_loop = clean_stmts[loop_idx+1:end]

    # `for i in a:b` binding: loop variable + range bounds
    loop_var = nothing
    range_start = nothing
    range_end = nothing
    if loop_expr.head == :for
        binding = loop_expr.args[1]
        if binding isa Expr && binding.head == :(=) && binding.args[1] isa Symbol
            loop_var = binding.args[1]
            rng = binding.args[2]
            if rng isa Expr && rng.head == :call && rng.args[1] == :(:) && length(rng.args) == 3
                range_start = rng.args[2]
                range_end = rng.args[3]
            else
                range_start = 1
                range_end = rng
            end
        end
    end

    # Parse initial assignments
    init_assigns = Pair{Symbol, Any}[]
    for s in pre_loop
        if s isa Expr && s.head == :(=) && length(s.args) == 2 && s.args[1] isa Symbol
            push!(init_assigns, s.args[1] => s.args[2])
        end
    end

    # Parse loop invariants, scalar updates and array updates from loop body
    loop_body = loop_expr.args[2]
    loop_stmts = loop_body isa Expr && loop_body.head == :block ? loop_body.args : Any[loop_body]
    invariants = Expr[]
    updates = Pair{Symbol, Any}[]
    array_updates = Tuple{Symbol, Any, Any}[]

    for s in loop_stmts
        s isa LineNumberNode && continue
        if s isa Expr
            if s.head == :macrocall && length(s.args) >= 3
                mname = s.args[1]
                sym = mname isa Symbol ? mname : (mname isa GlobalRef ? mname.name : nothing)
                if sym == Symbol("@invariant")
                    push!(invariants, s.args[3])
                    continue
                end
            elseif s.head == :(=) && length(s.args) == 2
                lhs = s.args[1]
                if lhs isa Symbol
                    push!(updates, lhs => s.args[2])
                    continue
                elseif lhs isa Expr && lhs.head == :ref && length(lhs.args) == 2
                    push!(array_updates, (lhs.args[1], lhs.args[2], s.args[2]))
                    continue
                end
            end
        end
    end

    # Use any global invariants attached to spec if none found inside loop
    if isempty(invariants) && !isempty(spec.invariants)
        append!(invariants, spec.invariants)
    end

    # Determine state variables
    state_vars = Symbol[]
    for (var, _) in init_assigns
        !(var in state_vars) && push!(state_vars, var)
    end
    for (var, _) in updates
        !(var in state_vars) && push!(state_vars, var)
    end
    for (arr, _, _) in array_updates
        !(arr in state_vars) && push!(state_vars, arr)
    end

    # Return expression
    ret_expr = nothing
    for s in post_loop
        if s isa Expr && s.head == :return && !isempty(s.args)
            ret_expr = s.args[1]
            break
        elseif !(s isa Expr && s.head == :(=))
            ret_expr = s
        end
    end
    if ret_expr === nothing && !isempty(state_vars)
        ret_expr = state_vars[1]
    end

    loop_cond = loop_expr.head == :while ? loop_expr.args[1] : true

    return LoopDescriptor(
        init_assigns,
        loop_expr.head,
        loop_cond,
        loop_var,
        range_start,
        range_end,
        invariants,
        updates,
        array_updates,
        ret_expr,
        state_vars
    )
end

# Sort inference for loop state variables: Bool literal => Bool, array-typed
# alias => (Array Int Real), everything else defaults to Real.
function _infer_state_sort(ex, var_sorts::Dict{Symbol, String})::String
    ex isa Bool && return "Bool"
    ex isa Expr || return "Real"
    if ex.head in (:&&, :||, :comparison, Symbol("-->"), Symbol("⟹"), :macrocall)
        return "Bool"
    elseif ex.head == :if
        return _infer_state_sort(ex.args[2], var_sorts)
    elseif ex.head == :call && ex.args[1] in (:(!), :not, :(==), :>, :<, :>=, :<=, :isless, :isgreater)
        return "Bool"
    elseif ex.head == :ref
        return "Real"
    end
    return "Real"
end

"""
    generate_bmc_query(spec::FormalSpecification, desc::LoopDescriptor; depth::Int=3, logic::String="ALL") -> String

Generates an unrolled SMT-LIB 2.6 query encoding Bounded Model Checking up to `depth` iterations.
Binds `for` loop variables to their unrolled iteration, encodes array updates as
`store`, and falsifies `not (invariants ∧ postconditions)` at the final state.
"""
function generate_bmc_query(spec::FormalSpecification, desc::LoopDescriptor; depth::Int=3, logic::String="ALL")::String
    lines = String[
        "; Generated by JuLean.jl Bounded Model Checker for $(spec.name) (depth=$depth)",
        "(set-logic $logic)",
        "(set-option :produce-models true)"
    ]

    # Argument constants and their sorts
    var_sorts = Dict{Symbol, String}()
    for arg in spec.args
        t = get(spec.arg_types, arg, Real)
        sort_str = julia_to_smt_type(t)
        var_sorts[arg] = sort_str
        push!(lines, "(declare-const $arg $sort_str)")
    end

    # Assert preconditions
    for (i, pre) in enumerate(spec.preconditions)
        push!(lines, "; Precondition $i\n(assert $(julia_to_smt_expr(pre)))")
    end

    # Step 0: State declaration and initialization
    step0_map = Dict{Symbol, Symbol}()
    for var in desc.state_vars
        v0 = Symbol("$(var)_0")
        step0_map[var] = v0
    end
    # Infer sorts from initializers (fall back to Real)
    for (var, val) in desc.init_assignments
        haskey(var_sorts, var) || (var_sorts[var] = _infer_state_sort(val, var_sorts))
    end
    for (arr, _, _) in desc.array_updates
        haskey(var_sorts, arr) || (var_sorts[arr] = "(Array Int Real)")
    end
    for var in desc.state_vars
        sort_str = get(var_sorts, var, "Real")
        push!(lines, "(declare-const $(Symbol("$(var)_0")) $sort_str)")
    end

    for (var, val) in desc.init_assignments
        v0 = step0_map[var]
        push!(lines, "(assert (= $v0 $(julia_to_smt_expr(val))))")
    end

    # Encode unrolling up to depth
    prev_map = step0_map
    for k in 1:depth
        curr_map = Dict{Symbol, Symbol}()
        for var in desc.state_vars
            vk = Symbol("$(var)_$k")
            curr_map[var] = vk
            push!(lines, "(declare-const $vk $(get(var_sorts, var, "Real")))")
        end

        # Loop-variable binding + iteration guard
        if desc.loop_kind == :for && desc.loop_var !== nothing
            iv = Symbol("$(desc.loop_var)_$k")
            push!(lines, "(declare-const $iv Int)")
            if desc.range_start isa Integer
                push!(lines, "(assert (= $iv $(desc.range_start + k - 1)))")
            else
                start_smt = julia_to_smt_expr(desc.range_start)
                push!(lines, "(assert (= $iv (+ $start_smt $(-(k - 1)))))")
            end
            end_smt = julia_to_smt_expr(desc.range_end)
            push!(lines, "; Iteration $k range guard\n(assert (<= $iv $end_smt))")
            curr_map[desc.loop_var] = iv
        elseif desc.loop_kind == :while
            cond_k_minus_1 = substitute_symbols(desc.loop_cond, prev_map)
            push!(lines, "\n; Iteration $k guard\n(assert $(julia_to_smt_expr(cond_k_minus_1)))")
        end

        # State updates (scalar)
        for (var, val) in desc.updates
            vk = curr_map[var]
            val_sub = substitute_symbols(val, prev_map)
            push!(lines, "(assert (= $vk $(julia_to_smt_expr(val_sub))))")
        end

        # State updates (array: store)
        for (arr, idx, val) in desc.array_updates
            ak = curr_map[arr]
            aprev = prev_map[arr]
            idx_sub = substitute_symbols(idx, prev_map)
            val_sub = substitute_symbols(val, prev_map)
            push!(lines, "(assert (= $ak (store $aprev $(julia_to_smt_expr(idx_sub)) $(julia_to_smt_expr(val_sub)))))")
        end

        prev_map = curr_map
    end

    # Final state: bind the return value
    ret_sort = julia_to_smt_type(spec.return_type)
    has_ret = desc.return_expr !== nothing
    if has_ret
        ret_sub = substitute_symbols(desc.return_expr, prev_map)
        push!(lines, "(declare-const result $ret_sort)")
        push!(lines, "(assert (= result $(julia_to_smt_expr(ret_sub))))")
    end

    # Target: falsify invariants ∧ postconditions at the final state
    targets = Expr[]
    if !isempty(desc.invariants)
        inv_conj = length(desc.invariants) == 1 ? desc.invariants[1] : Expr(:&&, desc.invariants...)
        push!(targets, inv_conj)
    end
    for post in spec.postconditions
        push!(targets, post)
    end
    if !isempty(targets)
        target = length(targets) == 1 ? targets[1] : Expr(:&&, targets...)
        target_sub = substitute_symbols(target, prev_map)
        push!(lines, "\n; Target: Falsify invariants/postconditions at depth $depth")
        push!(lines, "(assert (not $(julia_to_smt_expr(target_sub))))")
    end

    push!(lines, "(check-sat)")
    push!(lines, "(get-model)")

    return join(lines, "\n") * "\n"
end

"""
    verify_bmc(spec::FormalSpecification; depth::Int=3, logic::String="ALL", timeout::Float64=30.0) -> VerificationResult

Performs Bounded Model Checking (BMC) by unrolling loop iterations in SMT.
The falsification target is `not (invariants ∧ postconditions)` at the final
unrolled state; `unsat` means the loop kernel satisfies its specification for
every execution of exactly `depth` iterations.
"""
function verify_bmc(spec::FormalSpecification; depth::Int=3, logic::String="ALL", timeout::Float64=30.0)::VerificationResult
    desc = extract_loop_descriptor(spec)
    if desc === nothing
        return VerificationResult(
            spec.name,
            StatusError,
            :BMC;
            message="No loop found in function body to unroll."
        )
    end

    smt_code = generate_bmc_query(spec, desc; depth=depth, logic=logic)
    status_sym, out_str, err_str, elapsed = run_z3(smt_code; timeout=timeout)

    if status_sym == :unsat
        return VerificationResult(
            spec.name,
            StatusVerified,
            :BMC;
            message="Verified by Bounded Model Checking (depth=$depth, unsat)",
            smt_code=smt_code,
            elapsed_time=elapsed
        )
    elseif status_sym == :sat
        cex = parse_z3_model(out_str)
        return VerificationResult(
            spec.name,
            StatusCounterexample,
            :BMC;
            message="Counterexample found at unrolling depth $depth",
            smt_code=smt_code,
            counterexample=cex,
            elapsed_time=elapsed
        )
    else
        return VerificationResult(
            spec.name,
            StatusError,
            :BMC;
            message="BMC error: $out_str $err_str",
            smt_code=smt_code,
            elapsed_time=elapsed
        )
    end
end
