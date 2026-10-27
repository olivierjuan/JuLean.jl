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
