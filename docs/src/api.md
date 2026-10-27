# API Reference

## Contracts & Design-by-Contract

```@docs
JuLean.@contract
JuLean.@formalize
JuLean.@requires
JuLean.@ensures
JuLean.@invariant
JuLean.@forall
JuLean.@exists
JuLean.implies
JuLean.enable_contracts!
JuLean.disable_contracts!
JuLean.ContractViolationError
```

## Formal Specifications & Verification

```@docs
JuLean.FormalSpecification
JuLean.VerificationStatus
JuLean.VerificationResult
JuLean.is_verified
JuLean.verify
JuLean.verify_with_z3
JuLean.verify_bmc
JuLean.SPEC_REGISTRY
```

## Lean 4 Transpiler & Bridge

```@docs
JuLean.LeanType
JuLean.LeanExpr
JuLean.LeanDecl
JuLean.to_lean
JuLean.transpile_to_lean_decl
JuLean.synthesize_tactic
JuLean.register_lean_type!
JuLean.set_lean_project_dir!
JuLean.find_lean_project_dir
JuLean.run_lean
JuLean.LeanRunResult
```

## SMT & Bounded Model Checking

```@docs
JuLean.generate_smtlib_query
JuLean.run_z3
JuLean.LoopDescriptor
JuLean.extract_loop_descriptor
```

## Code Export & Tools

```@docs
JuLean.export_lean_file
JuLean.verification_summary
JuLean.simplify_expr
```

## Registries, Configuration & Introspection

```@docs
JuLean.STRUCT_REGISTRY
JuLean.CUSTOM_TYPE_REGISTRY
JuLean.LeanConfig
JuLean.find_lean_binary
JuLean.find_lake_binary
JuLean.extract_formal_spec
JuLean.extract_struct_decl
JuLean.julia_to_lean_type
JuLean.julia_to_lean_expr
```
