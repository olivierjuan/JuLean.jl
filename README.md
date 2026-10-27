# JuLean.jl

**Formal verification, design-by-contract, and interactive theorem proving bridge for Julia and Lean 4.**

JuLean.jl is a domain-agnostic meta-framework that lets you annotate Julia functions with
formal contracts, automatically search for counterexamples with Z3, transpile the annotated
code to Lean 4, and mechanically verify it against Mathlib theorems.

Scientific computing and operations-research solvers demand both high-throughput runtime
execution and strict mathematical correctness. JuLean bridges the two: floating-point
roundoff, subtle edge cases, and degenerate states no longer need to fail silently.

```julia
using JuLean

@formalize function clamp_flow(f::Real, lb::Real, ub::Real)::Real
    @requires lb <= ub
    @ensures lb <= result <= ub
    if f < lb
        return lb
    elseif f > ub
        return ub
    else
        return f
    end
end

verify(:clamp_flow; backend=:Z3)     # counterexample search via SMT (Z3)
verify(:clamp_flow; backend=:Lean4)  # mechanized proof via Lean 4 + Mathlib
```

## Features

- **Design-by-Contract** — `@requires`, `@ensures`, `@invariant` with a global
  zero-overhead toggle (`enable_contracts!` / `disable_contracts!`).
- **SMT falsification (Z3)** — direct SMT-LIB 2.6 generation, exact rational
  counterexample decoding, unsat-core extraction of essential preconditions, and
  bounded model checking (BMC) for loops.
- **Lean 4 transpilation** — Julia AST → Lean 4 AST → pretty-printed code, with an
  extensible type registry (`register_lean_type!`), exact rational (ℚ) projection,
  structs → `structure`, and quantifiers (`@forall`, `@exists`).
- **Mechanized verification** — runs `lake`/`lean` subprocesses against Mathlib and
  synthesizes proof scripts (`synthesize_tactic`). Proofs relying on `sorry` are
  reported as failures, never as verified.
- **Certified export** — serialize all registered definitions, theorems, and
  structures into standalone compilable Lean 4 files (`export_lean_file`).
- **Ecosystem integration** — optional Metatheory.jl extension for E-graph
  algebraic simplification (`simplify_expr`).

## Architecture

```
Annotated Julia (@formalize, @requires, ...)
        │
        v
Specification Extractor (FormalSpecification)
        │
        ├─> Level 0: Runtime contracts (zero-overhead toggle)
        ├─> Level 1: Z3 counterexample search (direct SMT-LIB 2.6)
        │                └─> BMC loop unrolling, unsat cores
        v
JuLean AST Transpiler (Julia AST -> Lean 4 AST)
        v
Lean 4 Code Generator (to_lean)
        v
Lean 4 Bridge (lake / lean subprocess)
        v
Mechanized proof (Mathlib, linarith, omega)
```

JuLean.jl is strictly domain-agnostic; it is designed as the verification core for
domain clients such as **Sirocco.jl** (generalized minimum-cost flow solvers) whose
mathematical theorems are formalized in the **DunesLean** Lean 4 library.

## Installation

```julia
using Pkg
Pkg.add(url = "https://gitlab.dunes.net/your-org/JuLean.jl")  # adjust to your remote
```

Requirements:

- Julia ≥ 1.10 (Z3 is provided automatically via `z3_jll`).
- For the `:Lean4` backend: [elan](https://github.com/leanprover/elan) with a Lean 4
  toolchain and a Lake project providing Mathlib (e.g. `mathlib4`), discoverable via
  `set_lean_project_dir!` or the `LEAN_PROJECT_DIR` environment variable.

## Usage

See the [documentation](docs/src/index.md) for the full guide:

- **Runtime contracts**: `@contract` with `@requires` / `@ensures` / `@invariant`.
- **Quantifiers**: `@forall(t::Real, (t <= x && t <= y) ⟹ t <= result)`.
- **Loop verification**: inductive invariants at runtime plus `verify(...; backend=:BMC)`
  for bounded model checking.
- **Export**: `export_lean_file("Formalization.lean")` produces a standalone,
  compilable Lean 4 module.

## Verification guarantees

| Backend | Guarantee |
| :--- | :--- |
| `:Z3` | No counterexample found within the encoded theory (not a proof of validity). |
| `:BMC` | No counterexample for loops unrolled up to depth `k`. |
| `:Lean4` | Mechanized proof accepted by the Lean 4 kernel; proofs containing `sorry` are **rejected**. |

## Development

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate(); Pkg.test()'

# Documentation
julia --project=docs -e 'using Pkg; Pkg.develop(path=pwd()); Pkg.instantiate(); include("docs/make.jl")'
```

See [ROADMAP.md](ROADMAP.md) for the project plan and current status.

## License

See the repository's licensing terms.
