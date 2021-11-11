using Plots
pyplot()
using BSON
using JSON
using Statistics
using Printf

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
        if isfile("results/$(name)_data.json")
            data = JSON.parse("results/$(name)_data.json")
            open("results/$(name)_frontier_length.json", "w") do f
                @printf f "%.3f" data["frontier_length"]
            end
        end
    end
end