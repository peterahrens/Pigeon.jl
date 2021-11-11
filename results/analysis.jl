using Plots
pyplot()
using BSON
using JSON
using Statistics

function main()
    names = [
        "bpcdd",
        "bpctd",
        "spgemm",
        "spgemm2",
        "sspgemm",
        "spgemmh",
        "spmv",
        "spmv2",
        "spmv3",
        "mttkrp",
    ]

    if !isdir("results")
        mkdir("results")
    end

    for name in names
        if isfile("$(name)_data.json")
        end
    end
end