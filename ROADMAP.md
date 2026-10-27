# JuLean.jl — Project Roadmap & Technical Specification

> **Language Mandate:** All documentation, code, test suites, docstrings, commit messages, and comments in this project are strictly written in **English**.

---

## 1. Executive Summary & Objectives

**JuLean.jl** is a formal verification, design-by-contract, and interactive theorem proving bridge connecting the **Julia** programming language with the **Lean 4** interactive theorem prover, supplemented by SMT solvers (Z3) and equality saturation (Metatheory.jl).

Scientific computing, operations research, and numerical optimization libraries (such as **Sirocco.jl** and **DuNeS**) require high-throughput runtime execution alongside strict mathematical correctness guarantees. Floating-point roundoff errors, subtle corner cases in graph pivots, and degenerate network states can produce silent correctness failures.

### Core Objectives
1. **Design-by-Contract (DbC):** Provide an expressive, zero-overhead annotation system (`@contract`, `@requires`, `@ensures`, `@invariant`) for Julia functions and data structures.
2. **Julia-to-Lean 4 Transpilation:** Automatically compile annotated Julia specifications and pure algorithms into idiomatic, typed Lean 4 definitions (`def`) and specification verification conjectures (`theorem ..._spec`).
3. **Automated & Interactive Verification Pipeline:**
   - **Level 0 (Dynamic DbC):** Runtime contract enforcement with zero runtime cost when disabled.
   - **Level 1 (SMT / Refutation):** Automated bounded checking and counterexample generation via Z3 / SMT-LIB before launching proof search.
   - **Level 2 (Term Rewriting):** AST canonicalization, algebraic normalization, and simplification using E-graphs (`Metatheory.jl`).
   - **Level 3 (Mechanized Proofs):** Automatic proof generation using Lean 4 tactics (`linarith`, `omega`, `decide`, `aesop`) and seamless export to the `DunesLean` formalization library.
4. **Target Domain Support:** Deep integration with exact rational optimization certificates ($\mathbb{Q}$), network simplex quasi-tree pivots, flow conservation equations, and dual feasibility conditions.

---

## 2. System Architecture & Verification Flow

```
                      +-----------------------------+
                      |     Annotated Julia Code    |
                      |   (@contract, @requires...) |
                      +--------------+--------------+
                                     |
                                     v
                      +-----------------------------+
                      |   Specification Extractor   |
                      |    (FormalSpecification)    |
                      +--------------+--------------+
                                     |
             +-----------------------+-----------------------+
             |                       |                       |
             v                       v                       v
     [ Level 0: Runtime ]   [ Level 1: SMT / Z3 ]  [ Level 2: Metatheory ]
     Dynamic assertion      Counterexample search  Equality saturation &
     checking via DbC       via Satisfiability.jl  term rewriting
             |                       |                       |
             +-----------------------+-----------------------+
                                     |
                                     v
                      +-----------------------------+
                      |  JuLean AST Transpiler      |
                      | (Julia AST -> Lean 4 AST)   |
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
                      | DunesLean Formalization Lib |
                      |  (Mathlib, QuasiTree, GMCF) |
                      +-----------------------------+
```

---

## 3. Feature Implementation Matrix

| Subsystem | Feature / Capability | Priority | Status | Description & Target Milestones |
| :--- | :--- | :---: | :---: | :--- |
| **Contracts** | Runtime Preconditions (`@requires`) | **P0** | Completed | Validates inputs prior to function execution; supports custom violation messages. |
| **Contracts** | Runtime Postconditions (`@ensures`) | **P0** | Completed | Captures function output in `result` and checks return invariants. |
| **Contracts** | Loop & State Invariants (`@invariant`) | **P0** | Completed | Verifies loop and internal state constraints during execution. |
| **Contracts** | Global Zero-Overhead Toggle | **P0** | Completed | `enable_contracts!` and `disable_contracts!` for zero production runtime overhead. |
| **Contracts** | Logical Operators (`implies`, `⟹`, `-->`) | **P0** | Completed | Standard classical implication operators with infix notation support. |
| **Core** | Module Entry Point (`src/JuLean.jl`) | **P0** | In Progress | Main module file re-exporting public API and configuring runtime defaults. |
| **Transpiler** | Lean 4 AST Representation | **P0** | Completed | Algebraic data types for Lean types (`LeanType`), expressions (`LeanExpr`), and decls (`LeanDecl`). |
| **Transpiler** | Julia AST to Lean 4 Converter | **P0** | Completed | Recursive converter handling blocks, let-bindings, calls, operators, and comparisons. |
| **Transpiler** | Lean 4 Code Generator (`to_lean`) | **P0** | Completed | Pretty printer producing indented, parenthesized Lean 4 source code. |
| **Transpiler** | Chained Comparison Expansion | **P0** | Completed | Converts expressions such as `lb <= x <= ub` into conjunctions `lb ≤ x ∧ x ≤ ub`. |
| **Transpiler** | Rational Number Projection ($\mathbb{Q}$) | **P0** | Completed | Casts Julia floating-point and rational values into exact Mathlib `ℚ` representations. |
| **Transpiler** | Variable Substitution for `result` | **P0** | Completed | Replaces `result` in postconditions with explicit function application calls. |
| **Lean Bridge** | Toolchain Auto-Detection | **P0** | Completed | Discovers `lean` and `lake` binaries under `~/.elan/bin` and system paths. |
| **Lean Bridge** | Subprocess Verification Runner | **P0** | Completed | Executes Lean 4 in isolated temporary environments with configurable timeout and diagnostics. |
| **Lean Bridge** | DunesLean Workspace Binding | **P1** | Completed | Links Lake projects with Mathlib dependencies in `dunes_lean4/formalization`. |
| **Verification** | Unified `@formalize` Macro | **P0** | In Progress | Single decorator combining runtime contract generation with automated Lean 4 compilation & verification. |
| **Verification** | Verification Result Diagnostics | **P0** | In Progress | Structured result object (`VerificationResult`) detailing status, proof script, counterexamples, and execution timing. |
| **Testing** | Unit & Integration Test Suite | **P0** | In Progress | Tests in `test/runtests.jl` covering contracts, transpiler correctness, and Lean 4 compiler invocation. |
| **SMT Backend** | Julia to SMT-LIB Transpiler | **P1** | Planned | Converts `FormalSpecification` into SMT-LIB constraints via `Satisfiability.jl`. |
| **SMT Backend** | Counterexample Extraction (Z3) | **P1** | Planned | Invokes `z3_jll` to find concrete input counterexamples when specifications are invalid. |
| **Metatheory** | Equality Saturation Normalizer | **P2** | Planned | Uses E-graphs (`Metatheory.jl`) to simplify Julia expressions into canonical algebraic forms prior to transpilation. |
| **Optimization** | Dunes / Sirocco Domain Primitives | **P1** | Planned | Pre-formalized Lean bindings for GMCF network structures, quasi-tree pivots, and optimality certificates. |
| **CI / CD** | Automated Verification Pipeline | **P1** | Planned | GitLab CI integration validating that all annotated functions verify against Lean 4 and Z3. |

---

## 4. Phased Milestones

### Phase 1: Foundations & Core Integration (v0.1.0) — *Current Phase*
- [x] Implement core contract system (`src/contracts.jl`).
- [x] Implement Lean 4 AST data structures (`src/transpiler/types.jl`).
- [x] Implement Julia AST to Lean 4 converter (`src/transpiler/julia_to_lean.jl`).
- [x] Implement Lean 4 pretty printer (`src/transpiler/printer.jl`).
- [x] Implement Lake and Lean compiler execution bridge (`src/lean_bridge.jl`).
- [ ] Create package root module (`src/JuLean.jl`) with clean public exports.
- [ ] Implement `@formalize` and `@verify` macros for interactive Julia REPL usage.
- [ ] Implement test suite (`test/runtests.jl`) covering contracts, transpilation, and Lean compiler execution.
- [ ] Initialize Git repository tracking and prepare initial commit.

### Phase 2: SMT-Based Counterexample Generation (v0.2.0)
- [ ] Implement `src/smt/smt_bridge.jl` translating `FormalSpecification` to SMT constraints.
- [ ] Integrate with `Satisfiability.jl` and `z3_jll`.
- [ ] Add pre-verification falsification pass: query Z3 before running Lean 4 proofs.
- [ ] Output human-readable Julia-level counterexample dictionaries on verification failure.

### Phase 3: Domain Specialization for Network Optimization (v0.3.0)
- [ ] Introduce formal definitions for Network Flow structures:
  - Node demands and flow conservation constraints.
  - Arc capacities, lower/upper bounds, and unit costs.
  - Multipliers and gain factors ($\gamma_a > 0$) for GMCF.
  - Quasi-tree basis partitions (tree arcs vs. cycle-forming arcs).
- [ ] Map exact rational certificates from `Sirocco.jl` to Lean 4 certificate structures in `DunesLean.Certificate`.
- [ ] Implement automated verification of dual feasibility ($c^\pi_a \ge 0$) and complementary slackness.

### Phase 4: Algebraic Rewriting & E-Graphs (v0.4.0)
- [ ] Integrate `Metatheory.jl` into the AST preprocessing pipeline.
- [ ] Define rewrite rules for arithmetic simplification (associativity, distributivity, rational canonicalization).
- [ ] Canonically reduce non-linear terms or simplify complex boolean preconditions before Lean / SMT export.

### Phase 5: Verified Synthesis & CI Integration (v1.0.0)
- [ ] Bidirectional verification: export verified Lean 4 theorems back into certified Julia implementations.
- [ ] Continuous formal verification in CI pipeline (`.gitlab-ci.yml`) ensuring zero regressions across both `Sirocco.jl` and `JuLean.jl`.
- [ ] Comprehensive documentation site generated with Documenter.jl.
