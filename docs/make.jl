using Documenter
using JuLean

makedocs(
    sitename = "JuLean.jl",
    authors = "Olivier Juan and JuLean Contributors",
    format = Documenter.HTML(
        prettyurls = get(ENV, "CI", nothing) == "true",
        canonical = "https://olivierjuan.github.io/JuLean.jl",
        collapselevel = 1,
        sidebar_sitename = true,
    ),
    modules = [JuLean],
    warnonly = [:missing_docs], # internal helpers (translate_*, parse_*) are not part of the public manual
    pages = [
        "Home" => "index.md",
        "User Guide" => "guide.md",
        "API Reference" => "api.md",
    ]
)

deploydocs(
    repo = "github.com/olivierjuan/JuLean.jl.git",
    devbranch = "main",
    push_preview = true,
)
