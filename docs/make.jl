using Documenter
using JuLean

makedocs(
    sitename = "JuLean.jl",
    format = Documenter.HTML(prettyurls = get(ENV, "CI", nothing) == "true"),
    modules = [JuLean],
    warnonly = [:missing_docs], # internal helpers (translate_*, parse_*) are not part of the public manual
    pages = [
        "Home" => "index.md",
        "User Guide" => "guide.md",
        "API Reference" => "api.md",
    ]
)
