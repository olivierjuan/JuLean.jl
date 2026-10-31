# User Guide & Verification Workflows

## 1. Design-by-Contract (DbC)

JuLean provides expressive macros for writing runtime and static contracts:

* `@requires condition [message]`: Input preconditions verified prior to body execution.
* `@ensures condition [message]`: Postconditions capturing the returned value in variable `result`.
* `@invariant condition [message]`: Invariants enforced on each iteration of loops and block states.
* Implication operators: `implies(p, q)`, `p ⟹ q`, `p --> q`.

### Global Toggle
For zero production overhead, disable runtime assertions:
```julia
disable_contracts!()
# Critical high-throughput loops run with zero assertion overhead
enable_contracts!()
```

---

## 2. Mathematical Quantifiers

Use `@forall` and `@exists` in contract expressions:

```julia
@formalize function find_min(x::Real, y::Real)::Real
    @requires x >= 0 && y >= 0
    @ensures @forall(t::Real, (t <= x && t <= y) ⟹ t <= result)
    return x < y ? x : y
end
```

* **In Julia:** Evaluated as `all(...)` / `any(...)` dynamically.
* **In Lean 4:** Transpiled to `∀ (t : ℚ), ...`
* **In SMT-LIB:** Transpiled to `(forall ((t Real)) ...)`

---

## 3. Composite Structures & Extensible Types

Annotate structs with `@formalize struct` to generate Lean 4 structures and SMT datatypes:

```julia
@formalize struct Interval
    lo::Real
    hi::Real
end

@formalize function span(iv::Interval)::Real
    @requires iv.lo <= iv.hi
    @ensures result >= 0
    return iv.hi - iv.lo
end
```

### Extensible Type Mapping
Client packages (like **Sirocco.jl**) can register domain-specific mappings:
```julia
register_lean_type!(GMCFProblem, "DunesLean.GMCFProblem")
```

---

## 4. Bounded Model Checking (BMC) for Loops

For iterative algorithms, unroll loops to depth $k$:

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

res = JuLean.verify(:loop_sum; backend=:BMC, depth=5)
```

If an iteration breaks the invariant, Z3 extracts the exact variable states at that step.

---

## 5. Unsat-Core Minimal Precondition Extraction

Z3 automatically isolates the minimal set of preconditions needed for verification:

```julia
res = JuLean.verify(:strict_positive; backend=:Z3)
println(res.unsat_core) # e.g. ["pre_1"]
```

---

## 6. Exporting Certified Artifacts

Export all verified structures and specifications into a standalone, compilable Lean 4 source file:

```julia
JuLean.export_lean_file("build/VerifiedModule.lean")
```

---

## 7. Non-Intrusive Contracts via Docstring Reflection

For high-performance packages (e.g. **Sirocco.jl**), you often want zero dependencies on `JuLean.jl` in your production codebase. JuLean provides a **docstring reflection engine** that reads contracts directly from standard Markdown docstrings:

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

In your package extension (loaded conditionally via `[weakdeps]`):
```julia
using JuLean
using MyPackage

# Reflect method AST and parse docstrings automatically:
JuLean.formalize!(MyPackage.reduced_cost)

# Verify with Z3 or Lean 4:
res = JuLean.verify(:reduced_cost; backend=:Z3)
```

---

## 8. Runtime Instrumentation & Assertion Stripping

Production kernels frequently contain internal contract checks or debug invariants (e.g., `_check_dual_equations!`). When transpiled to SMT or Lean 4, imperative error-throwing logic would fail to translate.

JuLean allows you to mark debug checks as **runtime-only**:

```julia
# Register debug guards and assertion functions
JuLean.register_runtime_only!(MyPackage._contracts_enabled)
JuLean.register_runtime_only!(MyPackage._check_bounds!)

# Statements calling these functions are automatically stripped from the formal AST
JuLean.formalize!(MyPackage.my_kernel)
```

Furthermore, JuLean automatically unwraps performance pragmas:
- `@inbounds`, `@simd`, `@inline`, `@noinline`, `@fastmath`, `@propagate_inbounds`

This guarantees that performance optimizations in Julia do not interfere with formal transpilation.

---

## 9. Function Inlining in Formal Specifications

When a formalized kernel calls auxiliary helper functions, JuLean can inline them automatically during SMT-LIB2 and Lean 4 generation:

```julia
# Define and register an inlinable helper:
@inline_formal function abs_diff(x::Real, y::Real)::Real
    return x >= y ? x - y : y - x
end

# Or register an existing function manually:
JuLean.register_inline!(:safe_div, [:num, :den], :(den != 0 ? num / den : 0))
```

Any call to `abs_diff` or `safe_div` inside a `@formalize` kernel is expanded into the kernel's expression tree prior to verification.

---

## 10. Imperative Code Transpilation & Lean 4 `Id.run do`

JuLean bridges imperative Julia algorithms to purely functional Lean 4 code using Lean 4's `Id.run do` monadic block:

* **In-Place Array Mutation:**
  `arr[idx] = val` in Julia transpires to `arr := arr.set! (idx - 1) val` in Lean 4.
* **Range Iteration:**
  `for i in 1:n` in Julia transpires to `for i in [:n] do` in Lean 4, with automatic 1-based to 0-based index translation.
* **While Loops:**
  `while count > 0` transpires to `while count > 0 do` with mutable state variables (`let mut`).
* **Compound Assignments:**
  `+=` and `-=` are translated into assignment rebindings.

```julia
@formalize function countdown(n::Int)::Int
    @requires n >= 0
    @ensures result == 0
    count = n
    while count > 0
        count -= 1
    end
    return count
end
```

Transpiles to Lean 4:
```lean
def countdown (n : Int) : Int :=
  Id.run do
    let mut count := n
    while count > 0 do
      count := count - 1
    return count
```

---

## 11. Equality Saturation & Metatheory.jl Integration

JuLean optionally integrates with `Metatheory.jl` via the `JuLeanMetatheoryExt` package extension. When `Metatheory.jl` is loaded in your environment:

```julia
using Metatheory
using JuLean

# Algebraic expressions are simplified using E-graph term rewriting:
expr = :(x + 0 * y + (z - z))
simplified = JuLean.simplify_expr(expr)
# => :x
```

