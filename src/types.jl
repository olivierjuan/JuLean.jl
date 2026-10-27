# JuLean.jl - Core Types and Verification Data Structures

"""
    ContractViolationError

Exception thrown when a precondition, postcondition, or invariant fails at runtime.
"""
struct ContractViolationError <: Exception
    kind::Symbol # :precondition, :postcondition, :invariant
    condition::String
    message::String
    func_name::Symbol
end

function Base.showerror(io::IO, err::ContractViolationError)
    print(io, "ContractViolationError [$(err.kind)] in `$(err.func_name)`: $(err.condition)")
    if !isempty(err.message)
        print(io, " ($(err.message))")
    end
end

"""
    FormalSpecification

Holds the extracted contract specification and metadata of an annotated Julia function.
"""
struct FormalSpecification
    name::Symbol
    args::Vector{Symbol}
    arg_types::Dict{Symbol, Any}
    return_type::Any
    preconditions::Vector{Expr}
    postconditions::Vector{Expr}
    invariants::Vector{Expr}
    body::Expr
    raw_ast::Expr
    docstring::String
end

function FormalSpecification(name::Symbol, args::Vector{Symbol}, body::Expr, raw_ast::Expr)
    return FormalSpecification(
        name,
        args,
        Dict{Symbol, Any}(),
        Any,
        Expr[],
        Expr[],
        Expr[],
        body,
        raw_ast,
        ""
    )
end

"""
    VerificationStatus

Status of a formal verification attempt.
"""
@enum VerificationStatus begin
    StatusVerified
    StatusCounterexample
    StatusUnverified
    StatusError
    StatusSyntaxChecked
end

"""
    VerificationResult

Outcome of verifying a specification using Lean 4, SMT/Z3, Metatheory, or Runtime testing.
"""
struct VerificationResult
    name::Symbol
    status::VerificationStatus
    backend::Symbol # :Lean4, :Z3, :Metatheory, :Runtime
    message::String
    lean_code::String
    smt_code::String
    counterexample::Union{Nothing, Dict{Symbol, Any}}
    unsat_core::Vector{String}
    elapsed_time::Float64
end

function VerificationResult(name::Symbol, status::VerificationStatus, backend::Symbol;
                            message::String="",
                            lean_code::String="",
                            smt_code::String="",
                            counterexample=nothing,
                            unsat_core::Vector{String}=String[],
                            elapsed_time::Float64=0.0)
    return VerificationResult(name, status, backend, message, lean_code, smt_code, counterexample, unsat_core, elapsed_time)
end

"""
    is_verified(res::VerificationResult) -> Bool

Returns `true` if the verification attempt succeeded, i.e. the specification
was proven valid (Lean 4) or no counterexample was found (Z3).
"""
function is_verified(res::VerificationResult)
    return res.status == StatusVerified
end

"""
    LeanConfig

Configuration for invoking the Lean 4 compiler and Lake build tool.
"""
Base.@kwdef mutable struct LeanConfig
    lean_cmd::String = ""
    lake_cmd::String = ""
    lean_path::Vector{String} = String[]
    project_dir::String = ""
    default_imports::Vector{String} = ["Mathlib.Tactic", "Mathlib.Algebra.BigOperators.Group.Finset.Basic"]
    timeout_seconds::Float64 = 60.0
end
