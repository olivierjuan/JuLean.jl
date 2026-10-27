# JuLean.jl - Formal Verification & Contract-Driven Synthesis Bridge for Julia & Lean 4

module JuLean

using MacroTools
using z3_jll

# Include core subsystems
include("types.jl")
include("contracts.jl")
include("lean_bridge.jl")

# Lean 4 AST & transpiler
include("transpiler/types.jl")
include("transpiler/julia_to_lean.jl")
include("transpiler/printer.jl")

# SMT / Z3 backend
include("smt/smt_printer.jl")
include("smt/z3_bridge.jl")
include("smt/bmc.jl")

# Lean 4 & certified artifact export
include("export.jl")

# Global specification registry for formalized functions
"""
    SPEC_REGISTRY

Global registry mapping function names (`Symbol`) to their extracted `FormalSpecification`.
Every function annotated with `@formalize` registers its specification here,
making it available to `verify`, `export_lean_file`, and `verification_summary`.
"""
const SPEC_REGISTRY = Dict{Symbol, FormalSpecification}()

"""
    simplify_expr(expr) -> Expr

Simplifies an algebraic expression. When `Metatheory.jl` is loaded,
the `JuLeanMetatheoryExt` extension performs equality saturation and term rewriting.
"""
function simplify_expr(expr)
    return expr
end

"""
    extract_formal_spec(fdef::Expr) -> FormalSpecification

Analyzes a Julia function definition expression, parses arguments, type annotations,
return type, docstring, and extracts all `@requires` and `@ensures` contracts.
"""
function extract_formal_spec(fdef::Expr)::FormalSpecification
    dict = MacroTools.splitdef(fdef)
    fn_name = dict[:name]
    args = Symbol[]
    arg_types = Dict{Symbol, Any}()

    for a in dict[:args]
        if a isa Symbol
            push!(args, a)
            arg_types[a] = Real
        elseif a isa Expr && a.head == :(::)
            sym = a.args[1]
            typ = a.args[2]
            push!(args, sym)
            arg_types[sym] = typ
        else
            push!(args, Symbol(string(a)))
            arg_types[Symbol(string(a))] = Real
        end
    end

    ret_type = get(dict, :rtype, Real)
    if ret_type === nothing
        ret_type = Real
    end

    pre, post, inv, clean_body = extract_contracts(dict[:body])

    return FormalSpecification(
        fn_name,
        args,
        arg_types,
        ret_type,
        pre,
        post,
        inv,
        clean_body,
        fdef,
        ""
    )
end

"""
    verify(spec::FormalSpecification; backend=:Z3, timeout=30.0, tactic="") -> VerificationResult

Verifies a `FormalSpecification` using the designated backend:
- `:Z3`: Rapid automated falsification and counterexample check via Z3 SMT solver.
- `:Lean4`: Mechanized proof verification using Lean 4 and Mathlib.
"""
function verify(spec::FormalSpecification; backend::Symbol=:Z3, timeout::Float64=30.0, tactic::String="", logic::String="", depth::Int=3)::VerificationResult
    if backend == :Z3
        return verify_with_z3(spec; logic=logic, timeout=timeout)
    elseif backend == :BMC
        return verify_bmc(spec; depth=depth, logic=(isempty(logic) ? "ALL" : logic), timeout=timeout)
    elseif backend == :Lean4
        lean_def, lean_thm = transpile_to_lean_decl(spec; tactic=tactic)
        struct_decls = [to_lean(s) for s in values(STRUCT_REGISTRY)]
        struct_header = isempty(struct_decls) ? "" : join(struct_decls, "\n\n") * "\n\n"
        code = struct_header * to_lean(lean_def) * "\n\n" * to_lean(lean_thm)
        run_res = run_lean(code; timeout=timeout)
        # Soundness: a proof that relies on `sorry` is NOT verified.
        # Lean reports `sorry` as a warning, so exit code 0 alone is not sufficient.
        uses_sorry = any(w -> occursin("sorry", lowercase(w)), run_res.warnings)
        status = (run_res.success && !uses_sorry) ? StatusVerified : StatusError
        if !run_res.success
            msg = isempty(run_res.errors) ? "Lean 4 exited with code $(run_res.exit_code)" : join(run_res.errors, "\n")
        elseif uses_sorry
            msg = "Proof relies on `sorry`; the theorem is not fully verified"
        else
            msg = "Verified by Lean 4"
        end
        return VerificationResult(
            spec.name,
            status,
            :Lean4;
            message=msg,
            lean_code=code,
            elapsed_time=run_res.elapsed_time
        )
    else
        error("Unsupported verification backend: $backend (choose :Z3 or :Lean4)")
    end
end

"""
    verify(fn_name::Symbol; backend=:Z3, kwargs...) -> VerificationResult

Verifies a registered function previously annotated with `@formalize`.
"""
function verify(fn_name::Symbol; kwargs...)
    if !haskey(SPEC_REGISTRY, fn_name)
        error("No formal specification found for `$fn_name`. Ensure it is annotated with `@formalize`.")
    end
    return verify(SPEC_REGISTRY[fn_name]; kwargs...)
end

"""
    @formalize function ... end
    @formalize struct ... end

Annotates a Julia function or struct definition with formal contracts:
- For `struct`: extracts the `LeanStructure`, registers it in `STRUCT_REGISTRY` & `CUSTOM_TYPE_REGISTRY`.
- For `function`: extracts `FormalSpecification`, instruments runtime contracts, and enables formal verification.
"""
macro formalize(def_expr)
    if def_expr isa Expr && def_expr.head == :struct
        lean_struct = extract_struct_decl(def_expr)
        sname = Symbol(lean_struct.name)
        return quote
            $(esc(def_expr))
            $(@__MODULE__).STRUCT_REGISTRY[$(QuoteNode(sname))] = $(esc(QuoteNode(lean_struct)))
            $(esc(QuoteNode(sname)))
        end
    end

    spec = extract_formal_spec(def_expr)
    dict = MacroTools.splitdef(def_expr)
    fn_name = dict[:name]
    pre, post, inv, clean_body = extract_contracts(dict[:body])

    dict[:body] = instrument_contract_body(fn_name, pre, post, clean_body)
    exec_expr = MacroTools.combinedef(dict)

    spec_quote = QuoteNode(spec)

    return quote
        $(esc(exec_expr))
        $(@__MODULE__).SPEC_REGISTRY[$(QuoteNode(fn_name))] = $(esc(spec_quote))
        $(esc(fn_name))
    end
end

# Exports
export
    # Contracts & DbC
    @contract,
    @formalize,
    @requires,
    @ensures,
    @invariant,
    @forall,
    @exists,
    implies,
    ⟹,
    -->,
    enable_contracts!,
    disable_contracts!,
    ContractViolationError,

    # Specifications & Verification
    FormalSpecification,
    VerificationStatus,
    StatusVerified,
    StatusCounterexample,
    StatusUnverified,
    StatusError,
    StatusSyntaxChecked,
    VerificationResult,
    is_verified,
    verify,
    SPEC_REGISTRY,

    # Lean 4 Transpiler & Bridge
    LeanType,
    LeanNat,
    LeanInt,
    LeanRat,
    LeanFloat,
    LeanBool,
    LeanString,
    LeanProp,
    LeanArray,
    LeanList,
    LeanFinset,
    LeanNamedType,
    LeanExpr,
    LeanVar,
    LeanLitInt,
    LeanLitRat,
    LeanLitFloat,
    LeanLitBool,
    LeanLitString,
    LeanApp,
    LeanBinOp,
    LeanUnaryOp,
    LeanIf,
    LeanLet,
    LeanFieldAccess,
    LeanIndexAccess,
    LeanDecl,
    LeanDef,
    LeanTheorem,
    LeanStructure,
    LeanInductive,
    to_lean,
    transpile_to_lean_decl,
    synthesize_tactic,
    julia_to_lean_type,
    julia_to_lean_expr,
    register_lean_type!,
    CUSTOM_TYPE_REGISTRY,
    STRUCT_REGISTRY,
    extract_struct_decl,
    set_lean_project_dir!,
    find_lean_project_dir,
    run_lean,
    LeanRunResult,
    LeanConfig,

    # SMT & Z3 Backend
    generate_smtlib_query,
    verify_with_z3,
    verify_bmc,
    LoopDescriptor,
    extract_loop_descriptor,
    run_z3,

    # Export & Artifacts
    export_lean_file,
    verification_summary,
    simplify_expr

end # module JuLean
