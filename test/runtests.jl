# JuLean.jl - Test Suite

using Test
using JuLean

@testset "JuLean.jl Formal Verification Test Suite" begin

    @testset "1. Logical Implication Operators" begin
        @test implies(true, true) == true
        @test implies(true, false) == false
        @test implies(false, true) == true
        @test implies(false, false) == true

        # Infix operator tests
        @test (true ⟹ true) == true
        @test (true ⟹ false) == false
        @test (false ⟹ true) == true
        @test (false ⟹ false) == true

        @test (true --> true) == true
        @test (true --> false) == false
    end

    @testset "2. Runtime Design-by-Contract (@contract)" begin
        @contract function compute_discount(price::Real, rate::Real)::Real
            @requires price >= 0 "Price must be non-negative"
            @requires 0 <= rate <= 1 "Rate must be in [0, 1]"
            @ensures 0 <= result <= price
            return price * (1 - rate)
        end

        # Valid inputs
        @test compute_discount(100.0, 0.2) ≈ 80.0
        @test compute_discount(0.0, 0.5) ≈ 0.0

        # Precondition failure: negative price
        @test_throws ContractViolationError compute_discount(-10.0, 0.2)

        # Precondition failure: invalid rate
        @test_throws ContractViolationError compute_discount(100.0, 1.5)

        # Contracts toggle: disable runtime checks
        disable_contracts!()
        @test compute_discount(-10.0, 2.0) ≈ -10.0 * (1 - 2.0)
        enable_contracts!(true)
        @test_throws ContractViolationError compute_discount(-10.0, 0.2)
    end

    @testset "3. Lean 4 AST Types & Code Generation" begin
        # Type generation
        @test to_lean(LeanNat()) == "Nat"
        @test to_lean(LeanInt()) == "Int"
        @test to_lean(LeanRat()) == "ℚ"
        @test to_lean(LeanArray(LeanRat())) == "Array (ℚ)"
        @test to_lean(LeanFinset(LeanNat())) == "Finset (Nat)"

        # Expression generation
        e_add = LeanBinOp(:+, LeanVar("x"), LeanLitRat(BigInt(1), BigInt(2)))
        @test to_lean(e_add) == "x + (1 : ℚ) / (2 : ℚ)"

        # Chained comparison expression
        comp_expr = JuLean.julia_to_lean_expr(:(lb <= x <= ub))
        @test occursin("≤", to_lean(comp_expr))
        @test occursin("∧", to_lean(comp_expr))

        # Extensible custom type registry
        struct MyCustomClientType end
        register_lean_type!(MyCustomClientType, "CustomClientModel")
        @test to_lean(julia_to_lean_type(MyCustomClientType)) == "CustomClientModel"
    end

    @testset "4. SMT-LIB2 Generation & Z3 Falsification" begin
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

        # Test valid function verification via Z3
        res_valid = JuLean.verify(:clamp_flow; backend=:Z3)
        @test res_valid.status == StatusVerified
        @test is_verified(res_valid)
        @test res_valid.backend == :Z3

        # Test buggy function counterexample extraction via Z3
        @formalize function buggy_clamp(f::Real, lb::Real, ub::Real)::Real
            @requires lb <= ub
            @ensures lb <= result <= ub
            # Bug: missing upper clamp
            if f < lb
                return lb
            else
                return f
            end
        end

        res_buggy = JuLean.verify(:buggy_clamp; backend=:Z3)
        @test res_buggy.status == StatusCounterexample
        @test !is_verified(res_buggy)
        @test res_buggy.counterexample !== nothing
        @test haskey(res_buggy.counterexample, :f)
        @test haskey(res_buggy.counterexample, :lb)
        @test haskey(res_buggy.counterexample, :ub)
    end

    @testset "5. Lean 4 & Lake Integration Bridge" begin
        lean_bin = JuLean.find_lean_binary()
        @test !isempty(lean_bin)
        @test isfile(lean_bin)

        # Run direct Lean 4 snippet
        direct_res = JuLean.run_lean("#check (42 : Nat)")
        @test direct_res.success
        @test direct_res.exit_code == 0

        # Verify clamp_flow formal specification in Lean 4
        res_lean = JuLean.verify(:clamp_flow; backend=:Lean4, tactic="by\n  unfold clamp_flow\n  split_ifs <;> constructor <;> linarith")
        @test res_lean.status == StatusVerified
        @test is_verified(res_lean)
        @test res_lean.backend == :Lean4
    end

    @testset "6. Composite Structs & Field Projections" begin
        @formalize struct Interval
            lo::Real
            hi::Real
        end

        @test haskey(JuLean.STRUCT_REGISTRY, :Interval)
        @test occursin("structure Interval", to_lean(JuLean.STRUCT_REGISTRY[:Interval]))

        @formalize function span(iv::Interval)::Real
            @requires iv.lo <= iv.hi
            @ensures result >= 0
            return iv.hi - iv.lo
        end

        # Test verification in Z3
        res_z3 = JuLean.verify(:span; backend=:Z3)
        @test res_z3.status == StatusVerified
        @test is_verified(res_z3)

        # Test verification in Lean 4
        res_lean = JuLean.verify(:span; backend=:Lean4, tactic="by\n  unfold span\n  linarith")
        @test res_lean.status == StatusVerified
        @test is_verified(res_lean)
    end

    @testset "7. Mathematical Quantifiers (@forall, @exists)" begin
        @formalize function min_val(x::Real, y::Real)::Real
            @requires x >= 0 && y >= 0
            @ensures @forall(t::Real, (t <= x && t <= y) ⟹ t <= result)
            return x < y ? x : y
        end

        # Verify with Z3
        res_z3 = JuLean.verify(:min_val; backend=:Z3)
        @test res_z3.status == StatusVerified
        @test is_verified(res_z3)

        # Verify with Lean 4
        res_lean = JuLean.verify(:min_val; backend=:Lean4, tactic="by\n  unfold min_val\n  intro t ht\n  split_ifs <;> linarith")
        @test res_lean.status == StatusVerified
        @test is_verified(res_lean)
    end

    @testset "8. Collections & Array Indexing" begin
        @formalize function safe_get(arr::Vector{Real}, i::UInt)::Real
            @requires 0 <= i < length(arr)
            @ensures result == arr[i]
            return arr[i]
        end

        # Verify with Z3
        res_z3 = JuLean.verify(:safe_get; backend=:Z3)
        @test res_z3.status == StatusVerified
        @test is_verified(res_z3)

        # Verify with Lean 4
        res_lean = JuLean.verify(:safe_get; backend=:Lean4, tactic="by\n  unfold safe_get\n  rfl")
        @test res_lean.status == StatusVerified
        @test is_verified(res_lean)

        # Bug detection with Z3
        @formalize function buggy_get(arr::Vector{Real}, i::UInt)::Real
            @requires 0 <= i < length(arr)
            @ensures result == arr[i]
            # Bug: returns element at index 0 regardless of i
            return arr[0]
        end

        res_buggy = JuLean.verify(:buggy_get; backend=:Z3)
        @test res_buggy.status == StatusCounterexample
        @test !is_verified(res_buggy)
    end

    @testset "9. Z3 Unsat-Core Minimal Precondition Extraction" begin
        @formalize function strict_positive(x::Real)::Real
            @requires x > 10.0            # Essential
            @requires x > -100.0          # Redundant
            @requires -500.0 < x          # Redundant
            @ensures result > 5.0
            return x + 1.0
        end

        res = JuLean.verify(:strict_positive; backend=:Z3)
        @test res.status == StatusVerified
        @test is_verified(res)
        @test !isempty(res.unsat_core)
        @test "pre_1" in res.unsat_core
        @test !("pre_2" in res.unsat_core)
        @test !("pre_3" in res.unsat_core)
    end

    @testset "10. Automated Proof Tactic Synthesis" begin
        # Verify function without supplying explicit `tactic` kwarg
        @formalize function auto_proved_span(iv::Interval)::Real
            @requires iv.lo <= iv.hi
            @ensures result >= 0
            return iv.hi - iv.lo
        end

        res_auto = JuLean.verify(:auto_proved_span; backend=:Lean4)
        @test res_auto.status == StatusVerified
        @test is_verified(res_auto)
        @test occursin("linarith", res_auto.lean_code)
    end

    @testset "11. Inductive Loop Invariants (@invariant)" begin
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

        spec = JuLean.SPEC_REGISTRY[:loop_sum]
        @test !isempty(spec.invariants)
        @test loop_sum(5) == 10

        # Test runtime invariant violation interception
        @formalize function faulty_loop(n::Int)::Int
            @requires n >= 0
            s = 0
            i = 0
            while i < n
                @invariant s >= 0
                s = s - 1 # breaks invariant
                i = i + 1
            end
            return s
        end

        @test_throws ContractViolationError faulty_loop(3)
    end

    @testset "12. Bounded Model Checking (BMC) for Loops" begin
        # Valid loop BMC verification
        res_bmc = JuLean.verify(:loop_sum; backend=:BMC, depth=3)
        @test res_bmc.status == StatusVerified
        @test is_verified(res_bmc)
        @test res_bmc.backend == :BMC

        # Faulty loop BMC counterexample detection
        res_faulty = JuLean.verify(:faulty_loop; backend=:BMC, depth=1)
        @test res_faulty.status == StatusCounterexample
        @test !is_verified(res_faulty)
        @test res_faulty.counterexample !== nothing
        @test haskey(res_faulty.counterexample, :s_1)
        @test res_faulty.counterexample[:s_1] == -1
    end

    @testset "13. Standalone Lean 4 File Export & Summary" begin
        tmp_lean = tempname() * ".lean"
        exported = export_lean_file(tmp_lean; fns=[:span, :auto_proved_span])
        @test isfile(tmp_lean)
        @test occursin("import Mathlib.Tactic", exported)
        @test occursin("structure Interval", exported)
        @test occursin("def span", exported)
        @test occursin("theorem span_spec", exported)

        # Ensure the exported standalone file compiles cleanly in Lean 4
        res_run = run_lean(exported)
        @test res_run.success
        @test res_run.exit_code == 0
        @test isempty(res_run.errors)
        rm(tmp_lean)

        # Verification summary output
        summary_str = verification_summary()
        @test occursin("JuLean.jl — Registered Formal Specifications Summary", summary_str)
        @test occursin("span", summary_str)
        @test occursin("clamp_flow", summary_str)
    end

    @testset "14. Metatheory E-Graph Simplification Extension" begin
        try
            @eval import Metatheory
            @test simplify_expr(:(x + 0)) == :x
            @test simplify_expr(:(0 + x)) == :x
            @test simplify_expr(:(x * 1)) == :x
            @test simplify_expr(:(x - x)) == 0
            @test simplify_expr(:((x * 1) + 0)) == :x
        catch
            @test simplify_expr(:(x + 0)) isa Expr
            @test simplify_expr(42) == 42
        end
    end

    @testset "15. Soundness: `sorry` never counts as verified" begin
        @formalize struct NegInterval
            lo::Real
            hi::Real
        end

        @formalize function fake_span(iv::NegInterval)::Real
            @requires iv.lo <= iv.hi
            @ensures result >= 0
            return iv.lo - iv.hi # BUG: result <= 0, the theorem is FALSE
        end

        # A `sorry`-based "proof" must NOT be reported as verified
        res_sorry = JuLean.verify(:fake_span; backend=:Lean4,
                                  tactic="by\n  unfold fake_span\n  first | linarith | sorry")
        @test res_sorry.status != StatusVerified
        @test !is_verified(res_sorry)
        @test occursin("sorry", res_sorry.message)

        # `synthesize_tactic` must be defined at module level and never emit `sorry`
        @test isdefined(JuLean, :synthesize_tactic)
        tactic = JuLean.synthesize_tactic(SPEC_REGISTRY[:fake_span])
        @test !occursin("sorry", tactic)

        # An honestly unprovable theorem must fail closed (no `sorry` escape hatch)
        res_fail = JuLean.verify(:fake_span; backend=:Lean4)
        @test res_fail.status == StatusError
        @test !is_verified(res_fail)
    end

    # 10. Imperative Programming & Id.run do Transpilation
    include("test_imperative.jl")

end
