# API Reference

## Contracts, Runtime Enforcement & Docstring Reflection

```@docs
JuLean.@contract
JuLean.@formalize
JuLean.formalize!
JuLean.contracted
JuLean.@requires
JuLean.@ensures
JuLean.@invariant
JuLean.requires
JuLean.ensures
JuLean.invariant
JuLean.@forall
JuLean.@exists
JuLean.implies
JuLean.enable_contracts!
JuLean.disable_contracts!
JuLean.CONTRACTS_ENABLED
JuLean.ContractViolationError
JuLean.extract_contracts
JuLean.parse_doc_contracts
JuLean.get_method_docstring
JuLean.auto_extract_method_ast
JuLean.instrument_contract_body
```

## Function Inlining & Runtime Instrumentation Stripping

```@docs
JuLean.@inline_formal
JuLean.register_inline!
JuLean.expand_inlines
JuLean.INLINE_REGISTRY
JuLean.register_runtime_only!
JuLean.strip_runtime_only
JuLean.RUNTIME_ONLY_REGISTRY
```

## Specifications, Verification & Domain Types

```@docs
JuLean.FormalSpecification
JuLean.PosInt
JuLean.VerificationStatus
JuLean.VerificationResult
JuLean.is_verified
JuLean.verify
JuLean.verify_with_z3
JuLean.verify_bmc
JuLean.SPEC_REGISTRY
JuLean.extract_formal_spec
JuLean.extract_struct_decl
```

## Lean 4 Transpiler, Monadic Blocks & AST Translation

```@docs
JuLean.LeanType
JuLean.LeanExpr
JuLean.LeanDecl
JuLean.LeanDoStmt
JuLean.to_lean
JuLean.to_lean_stmt
JuLean.transpile_to_lean_decl
JuLean.synthesize_tactic
JuLean.register_lean_type!
JuLean.julia_to_lean_type
JuLean.julia_to_lean_expr
JuLean.build_imperative_do_block
JuLean.build_lean_block
JuLean.is_imperative_block
JuLean.translate_call
JuLean.translate_comparison
JuLean.translate_lean_macro
JuLean.translate_1based_index
JuLean.substitute_symbols
JuLean.substitute_var
JuLean.is_pnat_type
JuLean.body_has_loops
JuLean.has_branching
JuLean.has_non_linear
JuLean.has_quantifier
JuLean.unwrap_ast_expr
```

## SMT-LIB2 Generation, Z3 & Bounded Model Checking

```@docs
JuLean.generate_smtlib_query
JuLean.generate_bmc_query
JuLean.run_z3
JuLean.parse_unsat_core
JuLean.parse_z3_model
JuLean.parse_smt_val
JuLean.translate_smt_call
JuLean.translate_smt_comparison
JuLean.translate_smt_macro
JuLean.build_smt_let_block
JuLean.unwrap_smt_expr
JuLean.julia_to_smt_expr
JuLean.julia_to_smt_type
JuLean.LoopDescriptor
JuLean.extract_loop_descriptor
```

## Toolchain Configuration & Lean 4 Runner

```@docs
JuLean.LeanConfig
JuLean.DEFAULT_LEAN_PROJECT_DIR
JuLean.set_lean_project_dir!
JuLean.find_lean_project_dir
JuLean.find_lean_binary
JuLean.find_lake_binary
JuLean.run_lean
JuLean.LeanRunResult
JuLean.STRUCT_REGISTRY
JuLean.CUSTOM_TYPE_REGISTRY
```

## Code Export & Term Rewriting

```@docs
JuLean.export_lean_file
JuLean.verification_summary
JuLean.simplify_expr
```
