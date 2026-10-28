using Test
using JuLean

@testset "Imperative Programming & Id.run do Transpilation" begin

    @testset "1. Array In-Place Mutation" begin
        @formalize function update_element(arr::Vector{Float64}, idx::Int, val::Float64)::Float64
            @requires idx >= 1
            arr[idx] = val
            return arr[idx]
        end

        spec = JuLean.SPEC_REGISTRY[:update_element]
        lean_def, _ = JuLean.transpile_to_lean_decl(spec)
        lean_code = JuLean.to_lean(lean_def)

        @test occursin("Id.run do", lean_code)
        @test occursin("let mut arr := arr", lean_code)
        @test occursin("arr := arr.set! (idx - 1).toNat val", lean_code)
        @test occursin("return arr[(idx - 1).toNat]!", lean_code)
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
        @formalize function find_lca_test(parent::Vector{Int}, depth::Vector{Int}, u::Int, v::Int)::Int
            @requires u >= 1 && v >= 1
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
        @test occursin("while depth[(curr_u - 1).toNat]! > depth[(curr_v - 1).toNat]! do", lean_code)
        @test occursin("while curr_u ≠ curr_v do", lean_code)

        res = JuLean.verify(:find_lca_test; backend=:Lean4, tactic="by\n  rfl")
        @test JuLean.is_verified(res)
    end

    @testset "6. Dynamic Array Construction (push! / Path Extraction)" begin
        @formalize function extract_path_test(parent::Vector{Int}, from_node::Int, ancestor::Int)::Vector{Int}
            @requires from_node >= 1 && ancestor >= 1
            curr = from_node
            path = Int[]
            while curr != ancestor && curr != 0
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

        res = JuLean.verify(:extract_path_test; backend=:Lean4, tactic="by\n  rfl")
        @test JuLean.is_verified(res)
    end

    @testset "7. Lean 4 Compilation of Transpiled Imperative Code" begin
        formal_path = normpath(joinpath(@__DIR__, "..", "..", "formalization"))
        if isdir(formal_path)
            tmp_lean = tempname() * ".lean"
            try
                open(tmp_lean, "w") do io
                    println(io, "import Mathlib.Tactic\n")

                    spec1 = JuLean.SPEC_REGISTRY[:update_element]
                    def1, _ = JuLean.transpile_to_lean_decl(spec1)
                    println(io, JuLean.to_lean(def1), "\n")

                    spec2 = JuLean.SPEC_REGISTRY[:accum_and_sub]
                    def2, _ = JuLean.transpile_to_lean_decl(spec2)
                    println(io, JuLean.to_lean(def2), "\n")

                    spec3 = JuLean.SPEC_REGISTRY[:find_lca_test]
                    def3, _ = JuLean.transpile_to_lean_decl(spec3)
                    println(io, JuLean.to_lean(def3), "\n")

                    spec4 = JuLean.SPEC_REGISTRY[:extract_path_test]
                    def4, _ = JuLean.transpile_to_lean_decl(spec4)
                    println(io, JuLean.to_lean(def4), "\n")
                end

                cmd = Cmd(`lake env lean $tmp_lean`, dir=formal_path)
                proc = run(pipeline(cmd; stdout=Pipe(), stderr=Pipe()); wait=false)
                stdout_str = read(proc.out, String)
                stderr_str = read(proc.err, String)
                wait(proc)

                @test proc.exitcode == 0
            finally
                rm(tmp_lean; force=true)
            end
        end
    end
end
