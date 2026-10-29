# JuLean.jl

```@raw html
<p align="center">
  <img src="assets/logo.svg" alt="JuLean.jl Logo" width="560">
</p>
```

*A Formal Verification and Design-by-Contract Bridge between Julia and Lean 4.*

---

## Overview

**JuLean.jl** bridges the high-performance scientific computing capabilities of **Julia** with the mechanized interactive theorem proving powers of **Lean 4**, supplemented by **SMT / Z3** for automated counterexample search and **E-graph equality saturation** for algebraic simplification.

JuLean is designed to be **100% domain-agnostic**: it can verify algorithms ranging from numerical optimization (such as **Sirocco.jl** and **DuNeS**) to abstract graph data structures and pure arithmetic routines.

---

## Multi-Tiered Verification Pipeline

JuLean implements a tiered verification architecture:

1. **Level 0 — Dynamic Design-by-Contract (DbC):**
   Zero-overhead runtime contract enforcement (`@contract`, `@requires`, `@ensures`, `@invariant`). Contracts can be toggled on/off globally with `enable_contracts!` / `disable_contracts!`.
2. **Level 1 — Rapid SMT Falsification (Z3):**
   Automated verification and counterexample search via native SMT-LIB 2.6 generation and `z3_jll`. Detects failing contracts and decodes exact rational counterexamples (`Rational{BigInt}`) in milliseconds.
3. **Level 2 — Bounded Model Checking (BMC):**
   Symbolic loop unrolling up to depth $k$ (`JuLean.verify(fn; backend=:BMC, depth=k)`) to verify invariant preservation and trace multi-step state violations.
4. **Level 3 — Mechanized Interactive Proofs (Lean 4):**
   Full deductive formal verification targeting Lean 4, Lake, and Mathlib. Generates typed definitions (`def`), specification conjectures (`theorem ..._spec`), and automatically synthesizes proof scripts using tactics (`linarith`, `omega`, `split_ifs`, `rfl`, `decide`).

---

## Quick Start

```julia
using JuLean

# 1. Define a function with formal contracts
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

# 2. Automated SMT / Z3 verification
res_z3 = JuLean.verify(:clamp_flow; backend=:Z3)
println(res_z3.status) # StatusVerified

# 3. Mechanized Lean 4 proof
res_lean = JuLean.verify(:clamp_flow; backend=:Lean4)
println(res_lean.status) # StatusVerified

# 4. Standalone Lean 4 file export
JuLean.export_lean_file("FormalModel.lean")
```
