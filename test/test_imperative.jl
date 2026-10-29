using Test
using JuLean

@testset "Imperative Programming & Id.run do Transpilation" begin

    @testset "1. Array In-Place Mutation" begin
        @formalize function update_element(arr::Vector{Float64}, idx::JuLean.PosInt, val::Float64)::Float64
            arr[idx] = val
            return arr[idx]
        end

        spec = JuLean.SPEC_REGISTRY[:update_element]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut arr := arr", lean_code)
        @test occursin("arr := arr.set! (idx.1 - 1) val", lean_code)
        @test occursin("return arr[(idx.1 - 1)]!", lean_code)

        # No postconditions: the def is type-checked only, nothing is proven.
        res = JuLean.verify(:update_element; backend=:Lean4)
        @test res.status == JuLean.StatusSyntaxChecked
        @test !JuLean.is_verified(res)
    end

    @testset "2. For Loop Over Range (1-based to 0-based mapping)" begin
        @formalize function sum_first_n(arr::Vector{Float64}, n::Int)::Float64
            @requires n >= 0
            total = 0.0
            for i in 1:n
                total += arr[i]
            end
            return total
        end

        spec = JuLean.SPEC_REGISTRY[:sum_first_n]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut total := (0 : ℚ)", lean_code)
        @test occursin("for i in [:n] do", lean_code)
        @test occursin("total := total + arr[i]!", lean_code)
        @test occursin("return total", lean_code)
    end

    @testset "3. While Loop Transpilation" begin
        @formalize function countdown(n::Int)::Int
            @requires n >= 0
            count = n
            while count > 0
                count -= 1
            end
            return count
        end

        spec = JuLean.SPEC_REGISTRY[:countdown]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut count := n", lean_code)
        @test occursin("while count > 0 do", lean_code)
        @test occursin("count := count - 1", lean_code)
        @test occursin("return count", lean_code)
    end

    @testset "4. Compound Assignment (+= and -=)" begin
        @formalize function accum_and_sub(x::Float64, y::Float64)::Float64
            acc = x
            acc += y
            acc -= 1.0
            return acc
        end

        spec = JuLean.SPEC_REGISTRY[:accum_and_sub]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut acc := x", lean_code)
        @test occursin("acc := acc + y", lean_code)
        @test occursin("acc := acc - (1 : ℚ)", lean_code)
        @test occursin("return acc", lean_code)
    end

    @testset "5. Tree Pointer Climbing (Lowest Common Ancestor - LCA)" begin
        @formalize function find_lca_test(parent::Vector{JuLean.NodeId}, depth::Vector{Int}, u::JuLean.NodeId, v::JuLean.NodeId)::JuLean.NodeId
            curr_u = u
            curr_v = v
            while depth[curr_u] > depth[curr_v]
                curr_u = parent[curr_u]
            end
            while depth[curr_v] > depth[curr_u]
                curr_v = parent[curr_v]
            end
            while curr_u != curr_v
                curr_u = parent[curr_u]
                curr_v = parent[curr_v]
            end
            return curr_u
        end

        spec = JuLean.SPEC_REGISTRY[:find_lca_test]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut curr_u := u", lean_code)
        @test occursin("let mut curr_v := v", lean_code)
        @test occursin("while depth[(curr_u.1 - 1)]! > depth[(curr_v.1 - 1)]! do", lean_code)
        @test occursin("while curr_u ≠ curr_v do", lean_code)

        # No postconditions: the def is type-checked only, nothing is proven.
        res = JuLean.verify(:find_lca_test; backend=:Lean4)
        @test res.status == JuLean.StatusSyntaxChecked
        @test !JuLean.is_verified(res)
    end

    @testset "6. Dynamic Array Construction (push! / Path Extraction)" begin
        @formalize function extract_path_test(parent::Vector{JuLean.NodeId}, from_node::JuLean.NodeId, ancestor::JuLean.NodeId)::Vector{JuLean.NodeId}
            curr = from_node
            path = JuLean.NodeId[]
            while curr != ancestor
                push!(path, curr)
                curr = parent[curr]
            end
            return path
        end

        spec = JuLean.SPEC_REGISTRY[:extract_path_test]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut path := #[]", lean_code)
        @test occursin("path := path.push curr", lean_code)

        # No postconditions: the def is type-checked only, nothing is proven.
        res = JuLean.verify(:extract_path_test; backend=:Lean4)
        @test res.status == JuLean.StatusSyntaxChecked
        @test !JuLean.is_verified(res)
    end

    @testset "8. PosInt / ℕ+ Indexing without toNat Casts" begin
        @formalize function pnat_indexing_test(
            potentials::Vector{Float64},
            nodes::Vector{PosInt},
            parent::Vector{PosInt},
            cost::Vector{Float64}
        )::Vector{Float64}
            for i in 1:length(nodes)
                node = nodes[i]
                p = parent[i]
                potentials[node] = potentials[p] + cost[i]
            end
            return potentials
        end

        spec = JuLean.SPEC_REGISTRY[:pnat_indexing_test]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        # Ensure Array ℕ+ is used and no .toNat casts are generated
        @test occursin("nodes : Array (ℕ+)", lean_code)
        @test occursin("parent : Array (ℕ+)", lean_code)
        @test occursin("(node.1 - 1)", lean_code)
        @test occursin("(p.1 - 1)", lean_code)
        @test !occursin("toNat", lean_code)

        # Soundness: a for-loop body with no postconditions must not be
        # reported as verified (Z3 drops loops; Lean has no theorem to prove).
        res_z3 = JuLean.verify(:pnat_indexing_test; backend=:Z3)
        @test res_z3.status == JuLean.StatusUnverified
        @test !JuLean.is_verified(res_z3)

        res_l4 = JuLean.verify(:pnat_indexing_test; backend=:Lean4)
        @test res_l4.status == JuLean.StatusSyntaxChecked
        @test !JuLean.is_verified(res_l4)
    end
end
