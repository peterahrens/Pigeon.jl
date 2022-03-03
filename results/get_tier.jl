using Plots
gr()
using BSON
using JSON
using Statistics
using Printf
using Pigeon

function main()
    names = [
        "spmv",
    ]
    rpath = "/Users/Peter/Projects/pldi2022/results"
    if !isdir(rpath)
        println("No output directory")
        exit()
    end

    for name in names
        if isfile("$(name)_bin.bson")
            data = BSON.load("$(name)_bin.bson")
            display(name)
            println()
            foreach(display, data["tacotier"])
            println()
        end
    end
end

main()
