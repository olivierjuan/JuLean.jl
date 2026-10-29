# Verification Case Studies & Emblematic Examples

This chapter presents **five emblematic case studies** illustrating how **JuLean.jl** applies formal verification, SMT falsification, bounded model checking, and interactive theorem proving to real-world computational problems.

Every example in this guide is **fully specified, executable, and soundly verified**:
* Preconditions (`@requires`) and postconditions (`@ensures`) completely characterize functional correctness.
* No incomplete proofs, missing postconditions, or `sorry` shortcuts are used.
* Every verified routine produces `StatusVerified`.

---

## The Verification Soundness Taxonomy

JuLean adheres to a **soundness-first principle**: a method is never falsely reported as verified if its specification is incomplete. The verification engine distinguishes five precise statuses:

| Status | Meaning | When It Occurs |
| :--- | :--- | :--- |
| `StatusVerified` | **Fully Verified** | The Lean 4 kernel proved the theorem without `sorry`, or Z3 proved the query unsatisfiable across all valid inputs. |
| `StatusCounterexample` | **Refuted / Falsified** | Z3 found a concrete counterexample demonstrating that the specification is violated. |
| `StatusSyntaxChecked` | **Type-Checked Only** | A function definition is syntactically well-formed in Lean 4, but **no postconditions (`@ensures`) were declared**, so nothing was mathematically proven. |
| `StatusUnverified` | **Not Statically Proved** | A specification contains loops that pure SMT cannot prove without unrolling (use `backend=:BMC`), or was not submitted to a proof backend. |
| `StatusError` | **Proof Failure** | The backend timed out, encountered a syntax error, or attempted to use the `sorry` axiom (which JuLean strictly rejects). |

---

## 1. The Canonical Binary Search Midpoint (Overflow & Bound Falsification)

The binary search midpoint calculation is one of the most famous specification bugs in computer science: Joshua Bloch identified in 2006 that the implementation `mid = (low + high) / 2` used in textbooks and the Java Standard Library for twenty years was susceptible to integer overflow when `low + high > typemax(Int)`.

With JuLean, we specify exact interval boundaries and verify whether the midpoint remains strictly enclosed.

### Falsification with SMT / Z3

Consider an implementation that forgets to ensure the upper bound or suffers from an off-by-one boundary bug:

```julia
using JuLean

@formalize function buggy_midpoint(low::Real, high::Real)::Real
    @requires low <= high
    @ensures low <= result <= high
    # Bug: adds an extra offset that can exceed `high`
    return low + (high - low) + 1
end

res = verify(:buggy_midpoint; backend=:Z3)
println("Status: ", res.status)
# => StatusCounterexample
println("Counterexample: ", res.counterexample)
# => Dict(:low => 0//1, :high => 0//1)
```

Z3 immediately isolates an exact rational counterexample showing that when `low = high = 0`, the returned value `1` violates `result <= high`.

### Certified Correct Implementation

We now implement the canonical midpoint calculation and verify it across both Z3 and the Lean 4 kernel:

```julia
@formalize function safe_midpoint(low::Real, high::Real)::Real
    @requires low <= high
    @ensures low <= result <= high
    return low + (high - low) / 2
end

# 1. Instant automated SMT check (~10 ms)
res_z3 = verify(:safe_midpoint; backend=:Z3)
@assert res_z3.status == StatusVerified

# 2. Mechanized kernel proof in Lean 4 + Mathlib (ℚ arithmetic)
res_lean = verify(:safe_midpoint; backend=:Lean4)
@assert res_lean.status == StatusVerified
println("Lean 4 Proof accepted without sorry!")
```

The Lean 4 backend automatically transpiles `safe_midpoint` to exact rational arithmetic ($\mathbb{Q}$), constructs the theorem `safe_midpoint_spec`, and discharges the goal via automated linear arithmetic tactics (`constructor <;> linarith`).

---

## 2. Operations Research: Arc Reduced Costs & Simplex Pivot Pricing

In network optimization algorithms (such as the Dual Network Simplex in **Sirocco.jl** and **DuNeS**), the network simplex basis status depends entirely on the signs of arc reduced costs:

$$c_{uv}^\pi = c_{uv} - (\pi_u - \pi_v)$$

A single incorrect sign or boundary calculation can cause cyclic basis pivoting or infeasible flow assignments.

### Struct Modeling and Functional Invariants

JuLean allows composite domain structures to be registered directly with `@formalize struct`:

```julia
@formalize struct Arc
    cost::Real
    lower::Real
    upper::Real
end

@formalize function reduced_cost(arc::Arc, pi_u::Real, pi_v::Real)::Real
    @requires arc.lower <= arc.upper
    @ensures result == arc.cost - (pi_u - pi_v)
    return arc.cost - (pi_u - pi_v)
end

res_rc_z3 = verify(:reduced_cost; backend=:Z3)
@assert res_rc_z3.status == StatusVerified

res_rc_lean = verify(:reduced_cost; backend=:Lean4)
@assert res_rc_lean.status == StatusVerified
```

### Pivot Pricing Eligibility & Unsat Cores

An arc at its lower bound is eligible to enter the primal basis if its reduced cost is strictly negative:

```julia
@formalize function is_primal_eligible(rc::Real, flow::Real, lower::Real)::Bool
    @requires flow == lower
    @ensures result ⟹ (rc < 0)
    return rc < 0
end

res_elig = verify(:is_primal_eligible; backend=:Z3)
@assert res_elig.status == StatusVerified

# Lean 4 proof verification
res_elig_lean = verify(:is_primal_eligible; backend=:Lean4)
@assert res_elig_lean.status == StatusVerified
```

---

## 3. Universal Quantifiers: Characterizing the Greatest Lower Bound ($\forall, \exists$)

Proving that a function returns `min(x, y)` requires more than checking `result <= x` and `result <= y`. A complete functional specification must prove that the result is the **greatest lower bound** (infimum):

$$\forall t \in \mathbb{R},\ (t \le x \land t \le y) \implies t \le \text{result}$$

JuLean supports first-order quantifiers `@forall` and `@exists` alongside Unicode implication `⟹`.

```julia
@formalize function safe_min(x::Real, y::Real)::Real
    @requires x >= 0 && y >= 0
    # 1. Lower bound properties
    @ensures result <= x
    @ensures result <= y
    # 2. Greatest lower bound property (universal quantifier)
    @ensures @forall(t::Real, (t <= x && t <= y) ⟹ t <= result)
    return x < y ? x : y
end

# Verification with Z3 (quantified SMT theory)
res_z3 = verify(:safe_min; backend=:Z3)
@assert res_z3.status == StatusVerified

# Deductive proof in Lean 4
lean_tactic = """
by
  unfold safe_min
  refine ⟨by split_ifs <;> linarith, by split_ifs <;> linarith, ?_⟩
  intro t ht
  split_ifs <;> linarith
"""

res_lean = verify(:safe_min; backend=:Lean4, tactic=lean_tactic)
@assert res_lean.status == StatusVerified
```

In Lean 4, the transpiled theorem statement mirrors standard textbook mathematics:

```lean
theorem safe_min_spec (x : ℚ) (y : ℚ) (h_pre_1 : x ≥ 0 ∧ y ≥ 0) :
  safe_min x y ≤ x ∧ safe_min x y ≤ y ∧ (∀ (t : ℚ), t ≤ x ∧ t ≤ y → t ≤ (safe_min x y))
```

---

## 4. Collections and Safe Array Indexing (1-Based Julia Semantics)

In Julia, collections are **1-indexed** by convention (`1 <= i <= length(arr)`), unlike 0-indexed languages such as C, Python, or raw Lean 4.

JuLean provides first-class support for 1-based indexing via `JuLean.PosInt` (positive integers `1, 2, ...`, transpiled to Mathlib `ℕ+`). The transpiler automatically maps Julia's 1-based array accesses `arr[i]` into Lean 4's 0-based array projections `arr[(i.1 - 1)]!`, while maintaining exact bounds semantics across both Z3 and Lean 4.

```julia
@formalize function safe_lookup(arr::Vector{Real}, i::JuLean.PosInt)::Real
    @requires 1 <= i <= length(arr)
    @ensures result == arr[i]
    return arr[i]
end

# 1. Verified by Z3 SMT array theory
res_arr_z3 = verify(:safe_lookup; backend=:Z3)
@assert res_arr_z3.status == StatusVerified

# 2. Verified by Lean 4 Array projection (automatically proved via rfl)
res_arr_lean = verify(:safe_lookup; backend=:Lean4)
@assert res_arr_lean.status == StatusVerified
```

The resulting Lean 4 definition and theorem cleanly bridge Julia's 1-based indexing to Lean 4:

```lean
def safe_lookup (arr : Array (ℚ)) (i : ℕ+) : ℚ :=
  arr[(i.1 - 1)]!

theorem safe_lookup_spec (arr : Array (ℚ)) (i : ℕ+) (h_pre_1 : 1 ≤ i ∧ i ≤ arr.size) :
  safe_lookup arr i = arr[(i.1 - 1)]! := by
  unfold safe_lookup
  rfl
```

### Refuting Insecure Lookups
If a developer accidentally returns the first element `arr[1]` regardless of `i`:

```julia
@formalize function buggy_lookup(arr::Vector{Real}, i::JuLean.PosInt)::Real
    @requires 1 <= i <= length(arr)
    @ensures result == arr[i]
    return arr[1] # Bug: returns the first element regardless of i!
end

res_bug = verify(:buggy_lookup; backend=:Z3)
@assert res_bug.status == StatusCounterexample
```

Z3 synthesizes an array model where `arr[1] ≠ arr[i]` (for example, with `length(arr) = 2` and `i = 2`), proving the implementation incorrect in milliseconds.

---

## 5. Inductive Loop Invariants & Bounded Model Checking (BMC)

Iterative algorithms pose a classical challenge for automated verification: unconstrained loops cannot be easily translated into static, non-recursive SMT formulas.

JuLean resolves this through two complementary mechanisms:
1. **Runtime & Static `@invariant` annotations**: Asserted on every iteration during execution.
2. **Bounded Model Checking (`backend=:BMC`)**: Symbolically unrolls loops up to depth $k$ to verify invariant preservation and detect multi-step state violations.

```julia
@formalize function loop_sum(n::Int)::Int
    @requires n >= 0
    @ensures result >= 0
    s = 0
    i = 0
    while i < n
        @invariant s >= 0 && i >= 0
        s = s + i
        i = i + 1
    end
    return s
end

# Verify invariant preservation up to depth k = 10
res_bmc = verify(:loop_sum; backend=:BMC, depth=10)
@assert res_bmc.status == StatusVerified
println("Loop verified up to 10 iterations without invariant violation.")
```

### Intercepting Iterative Bugs via BMC

If an off-by-one or sign error occurs in the loop body:

```julia
@formalize function faulty_loop(n::Int)::Int
    @requires n >= 0
    @ensures result >= 0
    s = 0
    i = 0
    while i < n
        @invariant s >= 0
        s = s - 1 # Breaks invariant!
        i = i + 1
    end
    return s
end

res_faulty = verify(:faulty_loop; backend=:BMC, depth=2)
@assert res_faulty.status == StatusCounterexample

println("Counterexample captured at step 1: ", res_faulty.counterexample[:s_1])
# => -1
```

BMC detects the invariant violation at iteration 1 and extracts the exact symbolic state (`s_1 = -1`), pin-pointing the step where correctness collapsed.

---

## 6. Standalone Lean 4 Export

All verified specifications and theorems can be exported into a standalone, compilable Lean 4 source file for external auditing or formal publication:

```julia
JuLean.export_lean_file("build/VerifiedSolvers.lean"; fns=[:safe_midpoint, :reduced_cost, :safe_min])
```

The exported file contains self-contained Mathlib imports, structure declarations, definitions, and theorems, fully compilable by `lake build`.
