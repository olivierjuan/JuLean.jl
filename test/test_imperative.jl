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

    @testset "5. Lean 4 Compilation of Transpiled Imperative Code" begin
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
