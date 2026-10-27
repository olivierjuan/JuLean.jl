# JuLean.jl - Z3 SMT Solver Execution & Counterexample Bridge

using z3_jll

"""
    parse_smt_val(s::AbstractString)

Parses an SMT-LIB scalar value representation (numbers, rationals, booleans) into Julia types.
"""
function parse_smt_val(s::AbstractString)
    clean = strip(s)
    if clean == "true"
        return true
    elseif clean == "false"
        return false
    end

    # Match negative rational: (- (/ 3.0 4.0)) or (- (/ 3 4))
    m_negrat = match(r"^\(\s*-\s*\(\s*/\s*([\d\.]+)\s+([\d\.]+)\s*\)\s*\)$", clean)
    if m_negrat !== nothing
        num = round(BigInt, parse(Float64, m_negrat.captures[1]))
        den = round(BigInt, parse(Float64, m_negrat.captures[2]))
        return -(num // den)
    end

    # Match positive rational: (/ 1.0 2.0) or (/ 1 2)
    m_posrat = match(r"^\(\s*/\s*([\d\.]+)\s+([\d\.]+)\s*\)$", clean)
    if m_posrat !== nothing
        num = round(BigInt, parse(Float64, m_posrat.captures[1]))
        den = round(BigInt, parse(Float64, m_posrat.captures[2]))
        return num // den
    end

    # Match negative number: (- 5) or (- 5.0)
    m_neg = match(r"^\(\s*-\s*([\d\.]+)\s*\)$", clean)
    if m_neg !== nothing
        val = parse(Float64, m_neg.captures[1])
        return isinteger(val) ? -round(Int, val) : -val
    end

    # Integer or float
    if tryparse(Int, clean) !== nothing
        return parse(Int, clean)
    elseif tryparse(Float64, clean) !== nothing
        val = parse(Float64, clean)
        return isinteger(val) ? round(Int, val) : val
    end

    return clean
end

"""
    parse_z3_model(out::AbstractString) -> Dict{Symbol, Any}

Extracts variable bindings from a Z3 `(get-model)` s-expression response.
"""
function parse_z3_model(out::AbstractString)::Dict{Symbol, Any}
    model = Dict{Symbol, Any}()
    idx = findfirst("(", out)
    idx === nothing && return model

    pos = 1
    while true
        m = match(r"\(define-fun\s+([a-zA-Z0-9_]+)\s*\(\)\s*([a-zA-Z0-9_]+)\s+", out, pos)
        m === nothing && break
        var_name = Symbol(m.captures[1])
        start_val = m.offset + length(m.match)

        val_str = ""
        if start_val <= length(out) && out[start_val] == '('
            # Parenthesized S-expression
            depth = 1
            i = start_val + 1
            while i <= length(out) && depth > 0
                if out[i] == '('
                    depth += 1
                elseif out[i] == ')'
                    depth -= 1
                end
                i += 1
            end
            val_str = strip(out[start_val:i-1])
            pos = i
        else
            # Simple token (number, boolean)
            m_tok = match(r"^[^\s\)]+", out[start_val:end])
            if m_tok !== nothing
                val_str = strip(m_tok.match)
                pos = start_val + length(m_tok.match)
            else
                pos = start_val + 1
            end
        end
        model[var_name] = parse_smt_val(val_str)
    end

    return model
end

"""
    run_z3(smt_code::String; timeout::Float64=30.0) -> (status::Symbol, stdout_str::String, stderr_str::String, elapsed::Float64)

Executes Z3 on the given SMT-LIB code string.
Returns `:sat`, `:unsat`, `:unknown`, or `:error`.
"""
function run_z3(smt_code::String; timeout::Float64=30.0)
    z3_bin = z3_jll.z3()
    cmd = `$z3_bin -smt2 -in`

    t0 = time()
    proc = open(cmd, "r+")
    write(proc, smt_code)
    close(proc.in)

    out_task = @async String(read(proc.out))
    err_task = @async (proc.err === nothing ? "" : String(read(proc.err)))

    start_time = time()
    while process_running(proc) && (time() - start_time < timeout)
        sleep(0.01)
    end

    if process_running(proc)
        kill(proc)
        return :timeout, "", "Z3 timed out after $(timeout)s", time() - t0
    end

    wait(proc)
    elapsed = time() - t0
    stdout_str = fetch(out_task)
    stderr_str = fetch(err_task)

    first_line = strip(first(split(stdout_str, "\n")))
    status_sym = if first_line == "sat"
        :sat
    elseif first_line == "unsat"
        :unsat
    elseif first_line == "unknown"
        :unknown
    else
        :error
    end

    return status_sym, stdout_str, stderr_str, elapsed
end

"""
    verify_with_z3(spec::FormalSpecification; logic::String="", timeout::Float64=30.0) -> VerificationResult

Verifies a specification using Z3.
- `unsat`: The specification holds for all inputs satisfying preconditions -> `StatusVerified`.
- `sat`: A counterexample violating postconditions was found -> `StatusCounterexample`.
- `unknown`: SMT solver was inconclusive -> `StatusUnverified`.
"""
function verify_with_z3(spec::FormalSpecification; logic::String="", timeout::Float64=30.0)::VerificationResult
    smt_code = generate_smtlib_query(spec; logic=logic)
    status_sym, out_str, err_str, elapsed = run_z3(smt_code; timeout=timeout)

    if status_sym == :unsat
        return VerificationResult(
            spec.name,
            StatusVerified,
            :Z3;
            message="Verified: No counterexample found (unsat)",
            smt_code=smt_code,
            elapsed_time=elapsed
        )
    elseif status_sym == :sat
        cex = parse_z3_model(out_str)
        return VerificationResult(
            spec.name,
            StatusCounterexample,
            :Z3;
            message="Counterexample found by Z3",
            smt_code=smt_code,
            counterexample=cex,
            elapsed_time=elapsed
        )
    elseif status_sym == :timeout
        return VerificationResult(
            spec.name,
            StatusUnverified,
            :Z3;
            message="Z3 timeout after $(timeout)s",
            smt_code=smt_code,
            elapsed_time=elapsed
        )
    else
        msg = isempty(err_str) ? out_str : err_str
        return VerificationResult(
            spec.name,
            StatusError,
            :Z3;
            message="Z3 error: $msg",
            smt_code=smt_code,
            elapsed_time=elapsed
        )
    end
end
