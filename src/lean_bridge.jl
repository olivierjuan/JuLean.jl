# JuLean.jl - Lean 4 & Lake Integration Bridge

"""
Result of a Lean 4 verification run.
"""
struct LeanRunResult
    success::Bool
    exit_code::Int
    stdout_output::String
    stderr_output::String
    errors::Vector{String}
    warnings::Vector{String}
    elapsed_time::Float64
end

"""
    find_lean_binary() -> String

Locates the `lean` compiler binary.
"""
function find_lean_binary()::String
    if haskey(ENV, "LEAN_PATH") && isfile(ENV["LEAN_PATH"])
        return ENV["LEAN_PATH"]
    end
    elan_lean = joinpath(homedir(), ".elan", "bin", "lean")
    if isfile(elan_lean)
        return elan_lean
    end
    which_lean = Sys.which("lean")
    if which_lean !== nothing
        return which_lean
    end
    return ""
end

"""
    find_lake_binary() -> String

Locates the `lake` build tool binary.
"""
function find_lake_binary()::String
    if haskey(ENV, "LAKE_PATH") && isfile(ENV["LAKE_PATH"])
        return ENV["LAKE_PATH"]
    end
    elan_lake = joinpath(homedir(), ".elan", "bin", "lake")
    if isfile(elan_lake)
        return elan_lake
    end
    which_lake = Sys.which("lake")
    if which_lake !== nothing
        return which_lake
    end
    return ""
end

"""
    find_formalization_dir() -> String

Finds the DunesLean formalization project directory if available.
"""
function find_formalization_dir()::String
    candidates = [
        "/home/D01856/dunes_lean4/formalization",
        joinpath(dirname(dirname(@__DIR__)), "formalization"),
        joinpath(dirname(dirname(@__DIR__)), "dunes_lean4", "formalization"),
        joinpath(pwd(), "formalization"),
        joinpath(pwd(), "dunes_lean4", "formalization")
    ]
    for c in candidates
        if isdir(c) && isfile(joinpath(c, "lakefile.toml"))
            return c
        end
    end
    return ""
end

"""
    run_lean(code::String; project_dir=find_formalization_dir(),
                           imports=["Mathlib.Tactic"],
                           set_options=["linter.unusedVariables false", "linter.unusedSectionVars false"],
                           timeout=60.0) -> LeanRunResult

Runs the Lean 4 compiler on the provided Lean code string and returns the result.
"""
function run_lean(code::String;
                  project_dir::String=find_formalization_dir(),
                  imports::Vector{String}=String["Mathlib.Tactic"],
                  set_options::Vector{String}=String["linter.unusedVariables false", "linter.unusedSectionVars false"],
                  timeout::Float64=60.0)::LeanRunResult
    lean_bin = find_lean_binary()
    lake_bin = find_lake_binary()

    if isempty(lean_bin)
        return LeanRunResult(false, -1, "", "Lean 4 binary not found. Please install Lean 4 via elan.", ["Lean 4 binary not found"], String[], 0.0)
    end

    # Construct complete source code
    import_lines = join(["import $imp" for imp in imports], "\n")
    option_lines = join(["set_option $opt" for opt in set_options], "\n")
    full_source = """
    $import_lines
    $option_lines

    $code
    """

    # Determine execution directory and command
    target_dir = isempty(project_dir) ? mktempdir() : project_dir
    temp_file = joinpath(target_dir, "julean_verify_$(rand(UInt32)).lean")

    write(temp_file, full_source)

    cmd = if !isempty(project_dir) && !isempty(lake_bin) && isfile(joinpath(project_dir, "lakefile.toml"))
        `$lake_bin -d $project_dir env $lean_bin $temp_file`
    else
        `$lean_bin $temp_file`
    end

    t0 = time()
    out_pipe = Pipe()
    err_pipe = Pipe()
    proc = run(pipeline(cmd, stdout=out_pipe, stderr=err_pipe), wait=false)

    # Read output asynchronously
    out_task = @async String(read(out_pipe))
    err_task = @async String(read(err_pipe))

    # Wait with timeout
    start_time = time()
    while process_running(proc) && (time() - start_time < timeout)
        sleep(0.05)
    end

    if process_running(proc)
        kill(proc)
        rm(temp_file, force=true)
        return LeanRunResult(false, -1, "", "Lean 4 process timed out after $(timeout)s", ["Timeout"], String[], time() - t0)
    end

    wait(proc)
    elapsed = time() - t0
    stdout_str = fetch(out_task)
    stderr_str = fetch(err_task)
    exit_code = proc.exitcode

    rm(temp_file, force=true)

    # Parse errors and warnings
    all_output = stdout_str * "\n" * stderr_str
    errors = String[]
    warnings = String[]

    for line in split(all_output, "\n")
        if occursin(": error:", line) || occursin("error: ", line)
            push!(errors, line)
        elseif occursin(": warning:", line) || occursin("warning: ", line)
            push!(warnings, line)
        end
    end

    success = (exit_code == 0) && isempty(errors)

    return LeanRunResult(success, exit_code, stdout_str, stderr_str, errors, warnings, elapsed)
end
