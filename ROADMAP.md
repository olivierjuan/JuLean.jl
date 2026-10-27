# JuLean.jl — Project Roadmap & Technical Specification

> **Language Mandate:** All documentation, code, test suites, docstrings, commit messages, and comments in this project are strictly written in **English**.

---

## 1. Executive Summary & Objectives

**JuLean.jl** is a **domain-agnostic** formal verification, design-by-contract (DbC), and interactive theorem proving bridge connecting the **Julia** programming language with the **Lean 4** interactive theorem prover, backed by automated SMT solving (Z3).

Scientific computing, numerical algorithms, and operations research solvers require high-throughput runtime execution alongside strict mathematical correctness guarantees. Floating-point roundoff errors, subtle edge cases, and degenerate states can produce silent correctness failures.

JuLean provides a generic meta-programming framework to annotate Julia algorithms with formal contracts, automatically extract their mathematical specifications, find counterexamples via Z3, transpile pure functions into Lean 4, and mechanically verify them against formal theorems.

### Separation of Concerns & Ecosystem Architecture
To ensure clean modularity and reusability, responsibilities are strictly separated across three layers:

1. **`JuLean.jl` (Generic Meta-Framework):**
   - 100% domain-agnostic. Contains **no** graph, network, or domain-specific algorithms.
   - Provides contracts (`@requires`, `@ensures`, `@invariant`), AST extraction, extensible type registration (`register_lean_type!`), Lean 4 AST generation, and Z3/Lake execution bridges.
2. **`Sirocco.jl` (Domain Client Solver):**
   - High-performance Julia solver for Generalized Minimum-Cost Flows (GMCF), network simplex on quasi-trees, and exact rational certificates.
   - Imports `JuLean` (`using JuLean`) to annotate its critical routines (pivot conditions, pricing rules, dual feasibility) and register its own domain types (`GMCFProblem`, `QuasiTree`, etc.).
3. **`DunesLean` (`formalization/` Lean 4 Library):**
   - Mechanized mathematical theorems (strong duality, quasi-tree basis properties, certificate validity) formalized in Lean 4 with Mathlib.

---

## 2. System Architecture & Verification Flow

```
                      +-----------------------------+
                      |     Annotated Julia Code    |
                      |   (@formalize, @requires...) |
                      +--------------+--------------+
                                     |
                                     v
                      +-----------------------------+
                      |   Specification Extractor   |
                      |    (FormalSpecification)    |
                      +--------------+--------------+
                                     |
             +-----------------------+-----------------------+
             |                                               |
             v                                               v
     [ Level 0: Runtime ]                           [ Level 1: SMT / Z3 ]
     Zero-overhead dynamic                          Automated falsification &
     contract enforcement                           counterexample search
     (enable/disable_contracts!)                    (direct SMT-LIB 2.6 / z3_jll)
             |                                               |
             +-----------------------+-----------------------+
                                     |
                                     v
                      +-----------------------------+
                      |  JuLean AST Transpiler      |
                      |  (Julia AST -> Lean 4 AST)  |
                      |  - Extensible Type Registry |
                      |  - Exact Rational (ℚ) Cast  |
                      +--------------+--------------+
                                     |
                                     v
                      +-----------------------------+
                      |    Lean 4 Code Generator    |
                      |      (to_lean printer)      |
                      +--------------+--------------+
                                     |
                                     v
                      +-----------------------------+
                      |   Lean 4 Bridge Runner      |
                      | (lake / lean subprocess API)|
                      +--------------+--------------+
                                     |
                                     v
                      +-----------------------------+
                      | Mechanized Proof in Lean 4  |
                      | (Mathlib, linarith, omega)  |
                      +-----------------------------+
```

---

## 3. Feature Implementation Matrix

| Subsystem | Feature / Capability | Priority | Status | Description & Target Milestones |
| :--- | :--- | :---: | :---: | :--- |
| **Contracts** | Runtime Preconditions (`@requires`) | **P0** | Completed | Validates function arguments before execution; supports custom violation messages. |
| **Contracts** | Runtime Postconditions (`@ensures`) | **P0** | Completed | Captures return value in `result` and asserts output properties. |
| **Contracts** | Loop & State Invariants (`@invariant`) | **P0** | Completed | Asserts invariants during loop execution or internal state updates. |
| **Contracts** | Global Zero-Overhead Toggle | **P0** | Completed | `enable_contracts!` and `disable_contracts!` for zero production runtime cost. |
| **Contracts** | Logical Implication (`implies`, `⟹`, `-->`) | **P0** | Completed | Classical logical implication with infix Unicode and ASCII operators. |
| **Core** | Module Entry Point (`src/JuLean.jl`) | **P0** | Completed | Central exports, specification registry (`SPEC_REGISTRY`), and `verify` dispatcher. |
| **Transpiler** | Lean 4 AST Representation | **P0** | Completed | Algebraic data types for Lean types (`LeanType`), expressions (`LeanExpr`), and decls (`LeanDecl`). |
| **Transpiler** | Julia AST to Lean 4 Converter | **P0** | Completed | Recursive converter handling blocks, let-bindings, calls, conditionals (`if`/`elseif`), and comparisons. |
| **Transpiler** | Extensible Type Registry (`register_lean_type!`) | **P0** | Completed | Allows client packages to register custom Julia types $\to$ Lean types dynamically. |
| **Transpiler** | Lean 4 Code Generator (`to_lean`) | **P0** | Completed | Pretty printer producing valid, parenthesized Lean 4 definitions and theorems. |
| **Transpiler** | Chained Comparison Expansion | **P0** | Completed | Converts expressions such as `lb <= x <= ub` into conjunctions `lb ≤ x ∧ x ≤ ub`. |
| **Transpiler** | Rational Number Projection ($\mathbb{Q}$) | **P0** | Completed | Casts Julia floating-point and rational values into exact Mathlib `ℚ` representations. |
| **Transpiler** | Variable Substitution for `result` | **P0** | Completed | Replaces `result` in postconditions with explicit function application calls. |
| **SMT Backend** | Julia to SMT-LIB Transpiler | **P0** | Completed | Lightweight direct SMT-LIB 2.6 generator (`src/smt/smt_printer.jl`) with zero external DSL dependencies. |
| **SMT Backend** | Counterexample Extraction (Z3) | **P0** | Completed | Invokes `z3_jll` directly and decodes model values into exact Julia rationals (`Rational{BigInt}`). |
| **Lean Bridge** | Toolchain Auto-Detection | **P0** | Completed | Discovers `lean` and `lake` binaries under `~/.elan/bin` and system paths. |
| **Lean Bridge** | Subprocess Verification Runner | **P0** | Completed | Non-blocking execution of Lake/Lean 4 with configurable timeouts and diagnostics parsing. |
| **Verification** | Unified `@formalize` Macro | **P0** | Completed | Single decorator combining runtime contract generation with automated Lean 4 compilation & verification. |
| **Verification** | Structured Result Diagnostics | **P0** | Completed | `VerificationResult` detailing verification status, backend, proof script, counterexamples, and timings. |
| **Testing** | Unit & Integration Test Suite | **P0** | Completed | Comprehensive test suite in `test/runtests.jl` covering contracts, transpiler, Z3, and Lean 4 (100% passing). |
| **Transpiler** | Julia `struct` to Lean `structure` Transpiler | **P0** | Completed | Transpiles pure Julia composite types into Lean 4 `structure` definitions with field projections. |
| **Verification** | Automated Quantifier Support ($\forall, \exists$) | **P0** | Completed | Expressive macro syntax for universal and existential quantifiers over collections, intervals, and sorts. |
| **Verification** | Collection Primitives & Array Indexing | **P0** | Completed | Multi-backend support for array lookups (`arr[i]`), bounds checks, and array size modeling. |
| **Verification** | Inductive Loop Verification | **P1** | Planned | Automatically translates loops with `@invariant` into inductive Lean 4 definitions and termination proofs. |
| **Metatheory** | Equality Saturation Extension | **P2** | Future | Optional package extension (`JuLeanMetatheoryExt`) for algebraic simplification via E-graphs. |
| **CI / CD** | Automated Continuous Verification | **P1** | Planned | GitLab CI integration validating that all annotated functions verify against Lean 4 and Z3. |

---

## 4. Phased Milestones

### Phase 1: Core Meta-Framework & Foundations (v0.1.0) — *Completed*
- [x] Implement core contract system (`@requires`, `@ensures`, `@invariant`, `implies`).
- [x] Implement Lean 4 AST data structures (`LeanType`, `LeanExpr`, `LeanDecl`).
- [x] Implement Julia AST to Lean 4 transpiler with operator and comparison expansion.
- [x] Implement domain-agnostic extensible type registry (`register_lean_type!`).
- [x] Implement Lean 4 code generator (`to_lean`).
- [x] Implement Lake and Lean compiler execution bridge (`src/lean_bridge.jl`).
- [x] Implement native SMT-LIB 2.6 generator and direct `z3_jll` runner (`src/smt/`).
- [x] Implement exact rational counterexample decoder.
- [x] Create package root module (`src/JuLean.jl`) with unified `@formalize` and `verify` APIs.
- [x] Implement automated test suite (`test/runtests.jl`) with 100% passing tests.

### Phase 2: Enhanced Language Expressivity & Data Structures (v0.2.0) — *Current Phase (In Progress)*
- [x] Implement `struct` transpilation: translate Julia `struct` definitions into Lean 4 `structure` declarations.
- [x] Add support for collection primitives (vectors, arrays) with indexed access properties and bounds contracts.
- [x] Add quantifier macros (`@forall`, `@exists`) for expressive specifications over collections and types.
- [ ] Implement inductive loop contract synthesis: translate `while` and `for` loops annotated with `@invariant` into recursive Lean definitions.

### Phase 3: Advanced Verification Tactics & Counterexample Analysis (v0.3.0)
- [ ] Automated tactic heuristic selector: choose between `linarith`, `omega`, `split_ifs`, `decide`, or `aesop` based on specification shape.
- [ ] Unsat-core extraction in Z3: report the minimal set of preconditions required for validity.
- [ ] Bounded model checking for loop invariants using SMT unrolling.

### Phase 4: Bi-directional Certified Synthesis & Tooling (v1.0.0)
- [ ] Optional E-graph rewrites via extension (`Metatheory.jl`) for non-linear algebraic canonicalization.
- [ ] Bidirectional verification: export verified Lean 4 lemmas back into certified Julia code comments or assertions.
- [ ] Continuous formal verification in CI pipeline (`.gitlab-ci.yml`).
- [ ] Complete documentation site generated with Documenter.jl.
