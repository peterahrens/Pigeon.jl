using Plots
gr()
using BSON
using JSON
using Statistics
using Printf
using Pigeon

function main()
    names = [
        "spgemm",
        "spgemm2",
        "spgemmh",
        "spmv",
        "spmv2",
        "smttkrp",
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
            display(data["auto_kernel"])
            println()
        end
    end
end

main()
