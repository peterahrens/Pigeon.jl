using Pigeon
using Documenter

DocMeta.setdocmeta!(Pigeon, :DocTestSetup, :(using Pigeon); recursive=true)

makedocs(;
    modules=[Pigeon],
    authors="Peter Ahrens",
    repo="https://github.com/peterahrens/Pigeon.jl/blob/{commit}{path}#{line}",
    sitename="Pigeon.jl",
    format=Documenter.HTML(;
        prettyurls=get(ENV, "CI", "false") == "true",
        canonical="https://peterahrens.github.io/Pigeon.jl",
        assets=String[],
    ),
    pages=[
        "Home" => "index.md",
    ],
)

deploydocs(;
    repo="github.com/peterahrens/Pigeon.jl",
)
