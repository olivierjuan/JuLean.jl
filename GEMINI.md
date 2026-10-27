# JuLean.jl — Project Conventions and Directives

## Language and Documentation Standards
- **English Only:** All code, comments, docstrings, documentation files (e.g., `README.md`, `ROADMAP.md`), test cases, error messages, and git commit messages MUST strictly be written in English.

## Architectural Mandates
- **Design-by-Contract:** Use `@contract`, `@requires`, `@ensures`, and `@invariant` for specifying function contracts and invariants.
- **Verification Pipeline:** Target Lean 4 (via `Lake` and `Mathlib`) as the primary interactive theorem proving backend, supplemented by SMT/Z3 (`Satisfiability.jl`) for counterexample finding.
- **Exact Arithmetic:** Numeric optimization variables and certificates use exact rational arithmetic (`ℚ` / `Rational{BigInt}`) to avoid floating-point inaccuracies.
- **Zero-Overhead Option:** Runtime contracts must be switchable with `enable_contracts!` / `disable_contracts!`.
