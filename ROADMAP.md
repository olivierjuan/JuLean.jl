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
| **Verification** | Inductive Loop Verification | **P0** | Completed | Extracts and enforces loop invariants (`@invariant`) at runtime and exports inductive VCs. |
| **Verification** | Automated Tactic Synthesis (`synthesize_tactic`) | **P0** | Completed | Heuristic proof script generator adapting to specification shapes, branches, and quantifiers. Defined at module level; its fallback chain never emits `sorry` (soundness). |
| **SMT Backend** | Minimal Unsat-Core Extraction (Z3) | **P0** | Completed | Automatic extraction of essential preconditions with named assertion tracking in SMT-LIB2. |
| **Verification** | Bounded Model Checking (BMC) for Loops | **P0** | Completed | Unrolls while/for loops to depth $k$ in SMT to verify invariant preservation and detect step bugs. |
| **Tooling** | Standalone Lean 4 Code Exporter | **P0** | Completed | Serializes all registered structs, definitions, and theorems to compilable Lean files (`export_lean_file`). |
| **Tooling** | Verification Summary Reporter | **P0** | Completed | Generates formatted overview tables (`verification_summary`) of contract counts and specification types. |
| **CI / CD** | Automated Continuous Verification | **P0** | Completed | GitLab CI pipeline (`.gitlab-ci.yml`) with unit/SMT jobs and a real Lean 4 verification gate backed by a cached Mathlib toolchain, plus GitLab Pages documentation deployment. |
| **Metatheory** | Equality Saturation Extension (`JuLeanMetatheoryExt`) | **P0** | Completed | Optional package extension for algebraic normalization and E-graph simplification via Metatheory.jl. |
| **Documentation** | Documentation Suite (`docs/`) | **P0** | Completed | Documenter.jl site with overview, user guide, and API reference; dedicated `docs/Project.toml`; built and deployed to GitLab Pages by CI. |

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

### Phase 2: Enhanced Language Expressivity & Data Structures (v0.2.0) — *Completed*
- [x] Implement `struct` transpilation: translate Julia `struct` definitions into Lean 4 `structure` declarations.
- [x] Add support for collection primitives (vectors, arrays) with indexed access properties and bounds contracts.
- [x] Add quantifier macros (`@forall`, `@exists`) for expressive specifications over collections and types.
- [x] Implement inductive loop contract synthesis: extract `@invariant` across `while` and `for` loops.

### Phase 3: Advanced Verification Tactics & Counterexample Analysis (v0.3.0) — *Completed*
- [x] Automated tactic heuristic selector: intelligent proof script generator adapting to branch splits, quantifiers, and arithmetic.
- [x] Unsat-core extraction in Z3: report the minimal set of preconditions required for validity.
- [x] Bounded model checking for loop invariants using SMT unrolling (`verify_bmc`).

### Phase 4: Bi-directional Certified Synthesis & Tooling (v0.4.0) — *Completed*
- [x] Bidirectional verification: export verified Lean 4 definitions, theorems, and structures into standalone compilable Lean files (`export_lean_file`).
- [x] Continuous formal verification in CI pipeline (`.gitlab-ci.yml`) — *upgraded to a real gate in Phase 5*.
- [x] Optional E-graph rewrites via extension (`JuLeanMetatheoryExt`) for algebraic canonicalization.
- [x] Complete documentation suite (`docs/`) with user guide, verification manual, and full API reference. *(build repaired in Phase 5)*

### Phase 5: Soundness Hardening, Packaging & Release Readiness (v1.0.0) — *Completed (October 2026)*
Discovered during the October 2026 project audit. All items below were resolved; the full test suite (100/100) and the Documenter build pass locally.

- [x] **Soundness fix (critical):** `verify(...; backend=:Lean4)` treated a Lean exit code 0 with no errors as a successful proof, but `sorry` only emits a *warning* — a demonstrably false theorem was reported as `StatusVerified`. Now any `sorry` warning fails verification (`StatusError`), and `sorry` was removed from the `synthesize_tactic` fallback chain (replaced by `norm_num`). Regression tests added (test set 15).
- [x] **Fixed broken function nesting in `src/transpiler/julia_to_lean.jl`:** `transpile_to_lean_decl` was missing its `end`, so `has_branching` and `synthesize_tactic` were accidentally nested inside it (`JuLean.synthesize_tactic` was exported yet undefined at module level).
- [x] **Repaired the Documenter build:** added missing docstrings (`is_verified`, `SPEC_REGISTRY`), extended the API manual (`STRUCT_REGISTRY`, `LeanConfig`, bridge utilities), added `docs/Project.toml` declaring Documenter, and set `warnonly = [:missing_docs]` for internal helpers. The build now exits 0.
- [x] **Added a top-level `README.md`** with project overview, installation, quickstart example, and links to the documentation.
- [x] **Removed machine-specific hardcoded paths** from `src/lean_bridge.jl`; project discovery now relies on `set_lean_project_dir!`, `LEAN_PROJECT_DIR` / `LAKE_PROJECT_DIR`, and relative path candidates only.
- [x] **Made the CI Lean 4 job a real gate:** the job now provisions Mathlib v4.35.0 via `lake exe cache get` (cached between runs), sets `LEAN_PROJECT_DIR`, and dropped `allow_failure: true`. Added a `pages` job deploying the documentation. *(Pipeline validated against the same toolchain versions locally; not yet exercised on a GitLab runner.)*
- [x] **Bumped `Project.toml` to version 1.0.0** with the full test suite and doc build passing.

### Phase 6: Ecosystem Integration with Sirocco.jl & DunesLean (v1.1.0) — *Current Phase*
- [ ] Annotate Sirocco.jl's critical routines (pivot conditions, pricing rules, dual feasibility) with JuLean contracts via `@formalize`.
- [ ] Register Sirocco domain types (`GMCFProblem`, `QuasiTree`, ...) through the extensible type registry (`register_lean_type!`).
- [ ] Link JuLean-exported specifications to hand-written Mathlib proofs in `DunesLean` (strong duality, quasi-tree basis properties, certificate validity).
- [ ] Cross-backend feedback loop: use Z3 counterexamples and unsat cores to suggest contract strengthening to the user.
