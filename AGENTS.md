# JuLean.jl — AI & LLM Agent Integration Guide

> **Target Audience:** Autonomous AI agents, LLM assistants (Gemini, Claude, GPT, Cursor, Copilot), and automated code generation systems modifying or integrating `JuLean.jl`.  
> **Core Mandate:** English only, zero production runtime overhead, non-intrusive formal layer, exact rational arithmetic ($\mathbb{Q}$), and strict mathematical soundness (zero `sorry` tolerance).

---

## 1. Executive Summary & Core Philosophy

`JuLean.jl` unifies **Design-by-Contract (DbC)**, **Automated SMT Falsification (Z3)**, and **Interactive Mechanized Proof (Lean 4 / Mathlib)** for Julia scientific and numerical code.

The guiding axiom of JuLean is:
> **"In numerical optimization and high-stakes scientific computing, speed without mathematical correctness is just faster bugs."**

When acting as an AI assistant to integrate JuLean into a package (such as `Sirocco.jl`, `Kaos.jl`, or any scientific solver), you must guarantee two non-negotiable properties:
1. **Zero Runtime Dependency Overhead:** Production users must never pay a runtime, compilation, or dependency penalty.
2. **Absolute Mathematical Soundness:** Proofs must be genuine, mechanized theorems without placeholders (`sorry`).

---

## 2. Canonical Integration Architecture: "Option A" (The Sirocco Pattern)

Never add `JuLean.jl` or `z3_jll` as direct dependencies in a solver's `[deps]` section. Instead, implement the **Option A package extension pattern** established in `Sirocco.jl`:

```
┌────────────────────────────────────────────────────────────────────────┐
│                   Tier 1: Core Solver (e.g. Sirocco.jl)                │
│  - src/simplex/pricing.jl, ratio_test.jl, solver.jl                    │
│  - 100% pure Julia, high-performance, generic typing                   │
│  - Contracts written in Markdown docstrings (ZERO JuLean dependency)   │
└────────────────────────────────────┬───────────────────────────────────┘
                                     │
                  Optional Dynamic Extension Trigger:
                       `using JuLean, MyPackage`
                                     │
                                     ▼
┌────────────────────────────────────────────────────────────────────────┐
│              Tier 2: Package Extension (ext/MyPackageJuLeanExt.jl)     │
│  - Registered via [weakdeps] in Project.toml                           │
│  - JuLean.formalize!(...) via docstring reflection                     │
│  - JuLean.register_lean_type!(...) for custom types / enums            │
│  - JuLean.register_runtime_only!(...) to strip debug checks            │
│  - Two-level verification runners (:Z3 and :Lean4)                     │
└────────────────────────────────────┬───────────────────────────────────┘
                                     │
                                     ▼
┌────────────────────────────────────────────────────────────────────────┐
│              Tier 3: Formal Verification Backends                      │
│  - Level 1: Z3 SMT solver (bundled via z3_jll, push-button falsification)│
│  - Level 2: Lean 4 + Mathlib (interactive / batch mechanized proofs)   │
└────────────────────────────────────────────────────────────────────────┘
```

### 2.1 Project.toml Configuration

In the client package's `Project.toml`:

```toml
[weakdeps]
JuLean = "60d1f2a1-a197-4d78-8ba3-1a6337fe4745"

[extensions]
MyPackageJuLeanExt = "JuLean"
```

For test environments, add `JuLean` to `[extras]` and include it in test targets.

---

## 3. Contract Authoring: Docstring Reflection

To keep the core solver free of macro dependencies, **write contracts directly in Markdown docstrings**. JuLean's reflection engine automatically parses docstrings at extension initialization time.

### 3.1 Docstring Syntax Standards

```julia
"""
    reduced_cost(cost, pi_u, pi_v, gamma)

Compute the generalized reduced cost of an arc.

- `@requires gamma > 0`
- `@ensures result == cost - pi_u + gamma * pi_v`
"""
function reduced_cost(cost, pi_u, pi_v, gamma)
    return cost - pi_u + gamma * pi_v
end
```

### 3.2 Formal Keywords & Conventions

| Keyword / Symbol | Meaning | Example |
| :--- | :--- | :--- |
| `- `@requires <expr>`` | Function precondition | `- `@requires lb <= ub && tol >= 0`` |
| `- `@ensures <expr>`` | Function postcondition | `- `@ensures result >= lb && result <= ub`` |
| `- `@invariant <expr>`` | Loop or state invariant | `- `@invariant s >= 0 && i >= 0`` |
| `result` | The returned value | `- `@ensures result == x + y`` |
| `⟹`, `-->`, `implies(p, q)` | Logical implication | `- `@ensures (dir == 1 ⟹ result <= ub)`` |
| `@forall(binding, cond)` | Universal quantifier | `- `@ensures @forall(e in 1:m, flow[e] >= 0)`` |
| `@exists(binding, cond)` | Existential quantifier | `- `@ensures @exists(v in 1:n, pi[v] == 0)`` |

### 3.3 Golden Rules for Contracts
- **Always use `result`** in `@ensures` to reference the return value of the function.
- **Do not write tautologies:** E.g., `@requires x > 0` followed by `@ensures x > 0` tests nothing about the function.
- **Avoid floating-point epsilons in contracts:** Prefer algebraic inequalities (`tol >= 0`, `delta == 0`) rather than `abs(x) < 1e-9`.

---

## 4. Stripping Runtime Checks: `register_runtime_only!`

In production solvers, kernels often include debug assertions or runtime integrity checks:

```julia
function ratio_step(f, bound, dir)
    if _contracts_enabled()
        _check_ratio_bounds(f, bound, dir)
    end
    return abs(bound - f)
end
```

If transpiled directly, SMT and Lean 4 engines will fail trying to parse imperative error-throwing logic.

### 4.1 How to Strip Runtime Checks Cleanly

In the extension's `__init__()`, register all debug guards and checker functions as **runtime-only**:

```julia
function __init__()
    # Register debug guards and assertion helpers
    JuLean.register_runtime_only!(MyPackage._contracts_enabled)
    JuLean.register_runtime_only!(MyPackage._check_ratio_bounds)

    # Formalize kernels after registering runtime-only helpers
    JuLean.formalize!(MyPackage.ratio_step)
end
```

**JuLean Mechanism:** JuLean's AST preprocessor recursively strips any statement containing a call to a registered runtime-only function. The production kernel retains its debug checks for testing, while the formal pipeline sees only the pure mathematical computation.

> **Note on Loops:** JuLean deliberately preserves `while` and `for` loops even if their body contains runtime-only calls; only the runtime statements *inside* the loop are removed.

### 4.2 Performance Pragmas Unwrapping
JuLean automatically unwraps macro pragmas:
- `@inbounds`, `@simd`, `@inline`, `@noinline`, `@fastmath`, `@propagate_inbounds`

You can use these performance annotations freely in production kernels. JuLean's AST parser unrolls them so they do not pollute the formal SMT or Lean 4 translation.

---

## 5. Exact Arithmetic ($\mathbb{Q}$) vs Floating-Point Fallacies

When building formal models or certificates:
- **Lean 4 and SMT operate over exact rationals ($\mathbb{Q}$ / `LeanRat`).**
- In Julia, test certificates and formal models must use `Rational{BigInt}` or exact integers (`Int64`).
- **Never** introduce `Float64` round-off tricks into formal contracts. If an algorithm requires a numerical tolerance, make `tol` an explicit parameter with `@requires tol >= 0`.

---

## 6. Architecture Partitioning: Micro-Kernels vs Imperative Driver Loops

A common failure mode for AI agents is trying to transpile an entire 500-line imperative `while`-loop solver into a single Lean 4 function. **Do not do this.**

Divide your solver into two distinct tiers:

### Tier A: Algorithmic Micro-Kernels (Transpiled AST)
- Examples: `reduced_cost`, `is_arc_eligible`, `ratio_step`, `update_flow`, `check_complementary_slackness`.
- Characteristics: Pure functions or localized in-place mutations.
- Verification: Transpiled automatically by JuLean into Lean 4 `def` + `theorem` declarations and verified via Z3 or automated tactics (`linarith`, `omega`, `split_ifs`).

### Tier B: Imperative Driver Loops (Inductive Step Bridge)
- Examples: `solve_simplex!`, `solve_dual_gmcf`.
- Characteristics: Outer `while` loop, mutable graph basis, early terminations, convergence tolerances.
- **The Step-Invariant Pattern:**
  1. Define an abstracted state structure in Lean 4 (`structure DriverState`).
  2. Define the inductive loop invariant (`def DriverInvariant : Prop`).
  3. Formulate the single-step preservation theorem (`theorem step_preserves_invariant`).
  4. Bridge to an existing formal library (such as `DunesLean` or `Mathlib`).
  5. Report the status honestly in Julia:
     - `:Z3` backend reports `StatusUnverified` (loops over dynamic structures are outside quantifier-free SMT scope).
     - `:Lean4` backend reports `StatusVerified` when the step bridge elaborates with zero `sorry`.

---

## 7. Custom Types, Inlining, and Proof Tactics

### 7.1 Registering Custom Types & Enums
If your Julia kernel uses an enum or struct:
```julia
JuLean.register_lean_type!(MyPackage.ArcStatus, "ArcStatus")
```

### 7.2 Inlining Helper Functions
If a kernel calls a small mathematical helper, register it for automatic inlining:
```julia
JuLean.register_inline!(:abs_diff, [:a, :b], :(a >= b ? a - b : b - a))
```

### 7.3 Supplying Lean 4 Proof Tactics
JuLean automatically synthesizes default tactics (`linarith`, `omega`, `split_ifs`). For non-trivial theorems, define a `KERNEL_TACTICS` dictionary in your extension:

```julia
const KERNEL_TACTICS = Dict{Symbol, String}(
    :reduced_cost =>
        """
        by
          unfold reduced_cost
          ring
        """,

    :ratio_step =>
        """
        by
          unfold ratio_step
          by_cases h : forward <;> simp [h] <;> rcases h_pre_1 with ⟨h1, h2, h3⟩ <;> linarith
        """,

    :cycle_root_potential =>
        """
        by
          unfold cycle_root_potential
          have h_denom : 1 - cycle_gain ≠ 0 := by
            intro h
            apply h_pre_1
            linarith
          exact div_mul_cancel₀ cycle_mismatch h_denom
        """
)
```

### 7.4 The Strict Soundness Rule: ZERO `sorry`
`JuLean.jl` explicitly inspects Lean compiler warnings and output. **Any proof that emits `sorry` is rejected with `StatusError`.** Never submit or generate `sorry` placeholders.

---

## 8. Implementing the Extension: Complete Template

Below is the idiomatic structure for `ext/MyPackageJuLeanExt.jl`:

```julia
module MyPackageJuLeanExt

using JuLean
using MyPackage

const KERNEL_FUNCTIONS = [
    MyPackage.reduced_cost,
    MyPackage.ratio_step,
    MyPackage.update_flow,
]

const KERNEL_NAMES = [nameof(f) for f in KERNEL_FUNCTIONS]

const KERNEL_TACTICS = Dict{Symbol, String}(
    :reduced_cost => "by unfold reduced_cost; ring",
    :ratio_step   => "by unfold ratio_step; split_ifs <;> linarith",
)

function __init__()
    # 1. Register types & enums
    JuLean.register_lean_type!(MyPackage.ArcStatus, "ArcStatus")

    # 2. Register runtime-only checks before formalizing
    JuLean.register_runtime_only!(MyPackage._contracts_enabled)
    JuLean.register_runtime_only!(MyPackage._check_bounds!)

    # 3. Formalize kernels from docstrings
    for f in KERNEL_FUNCTIONS
        JuLean.formalize!(f)
    end
end

"""
    MyPackage.verify_formal_specifications(; backend=:Z3, timeout=30.0)
"""
function MyPackage.verify_formal_specifications(; backend::Symbol=:Z3, timeout::Float64=30.0)
    results = Dict{Symbol, JuLean.VerificationResult}()
    for s in KERNEL_NAMES
        tac = get(KERNEL_TACTICS, s, "")
        results[s] = JuLean.verify(s; backend=backend, timeout=timeout, tactic=tac)
    end
    return results
end

"""
    MyPackage.export_lean_specifications(filepath::String)
"""
function MyPackage.export_lean_specifications(filepath::String)
    return JuLean.export_lean_file(filepath; fns=KERNEL_NAMES, tactics=KERNEL_TACTICS)
end

end # module MyPackageJuLeanExt
```

---

## 9. Verification Testing Pattern (`test/test_formal_verification.jl`)

Always provide comprehensive verification tests in the client package:

```julia
using Test
using JuLean
using MyPackage

@testset "JuLean Formal Verification" begin
    # 1. Verify extension loading and registry population
    @test isdefined(MyPackage, :verify_formal_specifications)
    for s in [:reduced_cost, :ratio_step]
        @test haskey(JuLean.SPEC_REGISTRY, s)
        spec = JuLean.SPEC_REGISTRY[s]
        @test !isempty(spec.postconditions)
        @test any(p -> occursin("result", string(p)), spec.postconditions)
    end

    # 2. Level 1: Z3 SMT Verification Sweep
    results_z3 = MyPackage.verify_formal_specifications(backend=:Z3)
    for (name, res) in results_z3
        @test JuLean.is_verified(res)
    end

    # 3. Level 2: Lean 4 Mechanized Proof Sweep (if Lean 4 installed)
    if JuLean.find_lean_project_dir() !== nothing
        results_lean = MyPackage.verify_formal_specifications(backend=:Lean4)
        for (name, res) in results_lean
            @test res.status == JuLean.StatusVerified
        end
    end
end
```

---

## 10. AI / LLM Quick Checklist: Do's and Don'ts

### ✅ DO:
1. **Adhere to Option A:** Keep the client package's `src/` 100% free of direct `using JuLean` statements.
2. **Use docstring contracts (`- `@requires ...``, `- `@ensures ...``)** in client code.
3. **Reference return values as `result`** in `@ensures` postconditions.
4. **Register all debug checks** with `JuLean.register_runtime_only!` before formalization.
5. **Decouple driver loops from micro-kernels:** Transpile micro-kernels; bridge drivers via step-invariants.
6. **Use exact rational arithmetic ($\mathbb{Q}$)** in certificates and formal specifications.
7. **Ensure zero `sorry`** in all Lean 4 tactics and bridge files.

### ❌ NEVER:
1. **Never add `JuLean` to `[deps]`** of a production library.
2. **Never hardcode floating-point epsilons** (`1e-9`, `1e-12`) into mathematical contracts.
3. **Never attempt to transpile full iterative state machines directly** with `extract_formal_spec`.
4. **Never accept or generate `sorry`** in Lean proofs.
5. **Never write tautological postconditions** that do not assert meaningful properties of `result`.
6. **Never leave runtime assertions active** during transpilation without registering them with `register_runtime_only!`.
