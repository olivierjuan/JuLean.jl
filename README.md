<div align="center">

<img src="assets/logo.svg" alt="JuLean.jl Logo" width="560">

<br>

**A unified Design-by-Contract, SMT Falsification, and Interactive Theorem Proving Bridge for Julia and Lean 4.**

[![Julia Version](https://img.shields.io/badge/julia-1.10%2B-9558B2.svg?logo=julia)](https://julialang.org)
[![Lean 4 Version](https://img.shields.io/badge/Lean_4-v4.35%2B-orange.svg?logo=lean)](https://lean-lang.org)
[![SMT Backend](https://img.shields.io/badge/SMT-Z3_bundled-blue.svg)](https://github.com/Z3Prover/z3)
[![CI](https://github.com/olivierjuan/JuLean.jl/actions/workflows/CI.yml/badge.svg)](https://github.com/olivierjuan/JuLean.jl/actions/workflows/CI.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub_Pages-blue.svg)](https://olivierjuan.github.io/JuLean.jl/)
[![Zero Overhead](https://img.shields.io/badge/production_overhead-0%25-success.svg)]()
[![Soundness](https://img.shields.io/badge/soundness-sorry--free-red.svg)]()
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

</div>

---

## Why JuLean?

Julia solved the **two-language problem**: scientific and numerical software can finally have the high-level elegance of Python and the raw speed of C.

However, in high-stakes numerical optimization, graph theory, computational geometry, and scientific computing, **speed without mathematical correctness is just faster bugs.** Silent floating-point overflows, degenerate basis cycles, boundary edge cases, and violated invariants can invalidate entire calculations without raising an error.

Interactive Theorem Provers (like **Lean 4** and **Mathlib**) provide mathematical certainty verified by a trusted microkernel, but formalizing algorithms by hand is historically disconnected from your production code.

**JuLean.jl unifies both worlds:**
1. **Specify naturally** — Express pre- and postconditions using Julian macros (`@requires`, `@ensures`, `@invariant`, `@forall`, `@exists`, `⟹`).
2. **Execute with Zero Cost** — Enforce contracts during development and testing, then toggle them off in production (`disable_contracts!()`) for **zero runtime overhead**.
3. **Falsify in milliseconds** — Search for counterexamples instantly via automated SMT solving with bundled Z3 (`z3_jll`, zero external dependencies). Get exact rational counterexamples (`Rational{BigInt}`) and minimal unsat-core preconditions.
4. **Transpile to Lean 4** — Seamlessly project Julia ASTs (including imperative loops and in-place array mutations!) into Lean 4 `structure`, `def`, and `theorem` declarations using exact Mathlib rationals ($\mathbb{Q}$).
5. **Mechanically Verify** — Let automated tactic synthesis (`linarith`, `omega`, `split_ifs`) or Lean 4's kernel construct machine-checked proofs. **Soundness guaranteed:** proofs with `sorry` are categorically rejected.

---

## The 4-Tier Verification Ladder

Verification is not all-or-nothing. JuLean provides a progressive ladder tailored to every stage of development:

```
[ Tier 0: Dynamic DbC ]          -->  Runtime contracts during testing; 0% cost in production
         │
         ▼
[ Tier 1: Automated SMT ]         -->  Push-button Z3 counterexample search & unsat cores (ms)
         │
         ▼
[ Tier 2: Bounded Model Check ]  -->  Symbolic loop unrolling up to depth k via SMT
         │
         ▼
[ Tier 3: Deductive Lean 4 ]     -->  Full mechanized kernel verification against Mathlib theorems
```

| Tier | Engine | Target | Guarantees | Latency | Production Overhead |
|:---|:---|:---|:---|:---|:---|
| **Tier 0: Dynamic DbC** | Julia Runtime | Execution paths in tests | Caught violations during test runs | Microseconds | **0%** (`disable_contracts!`) |
| **Tier 1: SMT Falsification** | Z3 (`z3_jll`) | All inputs in theory | Sound counterexample finding or validity | Milliseconds | Offline / CI |
| **Tier 2: Loop BMC** | SMT Unroller | Iterative loops | Invariant preservation up to depth $k$ | < 1 second | Offline / CI |
| **Tier 3: Mechanized Proof** | Lean 4 + Mathlib | Function specification | Machine-checked proof by Lean kernel | Seconds | Offline / CI |

---

## Quick Tour & Showcases

### 1. Guard, Falsify, and Prove in 5 Lines

Define an algorithm with mathematical contracts. JuLean extracts both the runtime assertions and the formal specification:

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

# Tier 1: Automated SMT check via Z3 (takes ~10 ms)
res_z3 = verify(:clamp_flow; backend=:Z3)
is_verified(res_z3)  # => true

# Tier 3: Mechanized proof in Lean 4 with auto-synthesized tactics
res_lean = verify(:clamp_flow; backend=:Lean4)
is_verified(res_lean) # => true (Kernel-certified!)
```

### 2. Instant Counterexample Discovery

What happens when an implementation has a subtle bug? Z3 finds an exact counterexample in milliseconds:

```julia
@formalize function buggy_clamp(f::Real, lb::Real, ub::Real)::Real
    @requires lb <= ub
    @ensures lb <= result <= ub
    # Bug: forgot the upper bound check!
    f < lb ? lb : f
end

res = verify(:buggy_clamp; backend=:Z3)

is_verified(res)          # => false
res.status                # => StatusCounterexample
res.counterexample        # => Dict(:f => 11//1, :lb => 0//1, :ub => 10//1)
```
Notice the values: JuLean decodes SMT models directly into **exact Julia rationals** (`Rational{BigInt}`), avoiding floating-point roundoff ambiguity!

---

### 3. Mathematical Expressiveness: Quantifiers & Unsat Cores

Write rich properties using `@forall`, `@exists`, and Unicode implication `⟹`:

```julia
@formalize function min_val(x::Real, y::Real)::Real
    @requires x >= 0 && y >= 0
    @ensures @forall(t::Real, (t <= x && t <= y) ⟹ t <= result)
    return x < y ? x : y
end

verify(:min_val; backend=:Lean4) # ✅ Proved automatically via tactic synthesis!
```

#### Minimal Preconditions (Unsat-Core Extraction)
JuLean automatically interrogates Z3 to identify which preconditions are strictly necessary:

```julia
@formalize function bounded_step(x::Real)::Real
    @requires x > 10.0   # Essential
    @requires x > -100.0 # Redundant
    @ensures result > 5.0
    return x + 1.0
end

res = verify(:bounded_step; backend=:Z3)
res.unsat_core  # => ["pre_1"] (identifies pre_2 as redundant!)
```

---

### 4. Real Imperative Julia Transpiled to Monadic Lean 4

Real-world high-performance Julia is rarely pure lambda calculus—it uses loops, index ranges, and in-place array mutations.

JuLean transpiles **idiomatic imperative Julia** into Lean 4's monadic `Id.run do` notation with `let mut`:

```julia
@formalize function sum_first_n(arr::Vector{Float64}, n::Int)::Float64
    @requires n >= 0
    total = 0.0
    for i in 1:n
        total += arr[i]
    end
    return total
end
```

Transpiles directly to clean, idiomatic Lean 4:

```lean
def sum_first_n (arr : Array (ℚ)) (n : Int) : ℚ :=
  Id.run do
    let mut total := (0 : ℚ)
    for i in [:n] do
      total := total + arr[i]!
    return total
```

In-place mutations like `arr[i] = val` are transparently mapped to functional updates (`arr := arr.set! (i - 1) val`), reconciling Julian speed with functional proof semantics.

---

### 5. Non-Invasive Docstring Contracts

Already have an existing codebase? You don't need to rewrite your functions. Annotate them directly in standard Julia Markdown docstrings:

```julia
"""
    reduced_cost(cost, pi_u, pi_v)

Computes the reduced cost of an arc `(u, v)`.
- `@requires cost >= 0`
- `@ensures result == cost - (pi_u - pi_v)`
"""
reduced_cost(cost, pi_u, pi_v) = cost - (pi_u - pi_v)

# Formalize without altering the function definition!
@formalize reduced_cost

verify(:reduced_cost; backend=:Z3) # ✅ StatusVerified
```

---

### 6. Zero-Cost Abstraction in Production

Contracts are invaluable during testing and verification, but tight optimization loops cannot afford runtime branching. JuLean provides a global zero-cost switch:

```julia
using JuLean

# Enable in development and test suites
enable_contracts!(true)

# In production / release builds:
disable_contracts!()
# All contract guards are stripped at runtime with 0% CPU overhead.
```

---

### 7. Certified Artifact Export

Need to share or archive formal specifications? Export all registered structs, definitions, and theorems into a standalone, compilable Lean 4 source file:

```julia
JuLean.export_lean_file("build/FormalModel.lean")
```

The resulting file imports Mathlib, declares `structure` definitions for your Julia structs, emits pure `def` functions, and formulates formal `theorem` statements ready for interactive proving in VS Code or Lake.

---

## Ecosystem & Composability

JuLean is strictly domain-agnostic and designed to act as the verification substrate for scientific packages:

* **[Metatheory.jl](https://github.com/JuliaSymbolics/Metatheory.jl) Integration** — Through the `JuLeanMetatheoryExt` package extension, JuLean supports algebraic simplification and equality saturation via E-graphs (`simplify_expr`).
* **Extensible Type Registry** — Client solvers (such as [Sirocco.jl](https://github.com/dunes-net/Sirocco.jl) for Generalized Minimum-Cost Flows) can register their custom domain structures using `register_lean_type!(MyType, "LeanTypeName")`.
* **Standard Binary Artifacts** — Thanks to `z3_jll`, SMT verification requires **zero setup**: no manual Z3 compilation, no PATH tweaking. It works out-of-the-box on Linux, macOS, and Windows.

---

## Verification Guarantees & Soundness Policy

> **The "No `sorry`" Principle:**
> In Lean 4, unproven conjectures can be temporarily discharged using the `sorry` axiom, which produces a compiler warning rather than an error.
>
> **JuLean rejects `sorry` categorically.** If a proof script relies on `sorry` or an unproven theorem, verification status is marked as `StatusError`. A function is only reported as `StatusVerified` when checked and accepted by the Lean 4 kernel without escape hatches.

---

## Installation

JuLean.jl is a standard Julia package:

```julia
using Pkg
Pkg.add(url = "https://gitlab.dunes.net/dunes/JuLean.jl") # Or add JuLean once in General registry
```

### Requirements:
* **Julia ≥ 1.10**
* **SMT Backend (Z3):** Works immediately with zero configuration (provided automatically via `z3_jll`).
* **Lean 4 Backend (Optional):** Requires [elan](https://github.com/leanprover/elan) with a Lean 4 toolchain and a Lake project providing Mathlib (e.g. `mathlib4`). Configure the directory with:
  ```julia
  using JuLean
  set_lean_project_dir!("/path/to/my_lean_project")
  ```
  or set the `LEAN_PROJECT_DIR` environment variable.

---

## Running the Test Suite

JuLean comes with a comprehensive test suite covering contracts, transpilation, Z3 counterexamples, BMC, and Lean 4:

```bash
julia --project=. -e 'using Pkg; Pkg.test()'
```

To build the documentation locally with Documenter.jl:

```bash
julia --project=docs -e 'using Pkg; Pkg.develop(path=pwd()); Pkg.instantiate(); include("docs/make.jl")'
```

---

## Contributing & Community

Contributions, issue reports, and RFCs are welcome!
* Follow the [ROADMAP.md](ROADMAP.md) to see planned features and upcoming milestones.
* All code, comments, docstrings, and documentation follow the **English-only** convention.

## License

JuLean.jl is open-source software licensed under the **MIT License**.
