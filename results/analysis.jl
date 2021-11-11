using Plots
gr()
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
        if isfile("$(name)_data.json")
            data = Dict()
            open("$(name)_data.json", "r") do f
                data = JSON.parse(f)
            end
            open("results/$(name)_frontier_length.json", "w") do f
                @printf f "%.3g" data["frontier_length"]
            end
            open("results/$(name)_universe_length.json", "w") do f
                @printf f "%.3g" data["universe_length"]
            end
            open("results/$(name)_tacotier_length.json", "w") do f
                @printf f "%.3g" data["tacotier_length"]
            end
            open("results/$(name)_tacoverse_length.json", "w") do f
                @printf f "%.3g" data["tacoverse_length"]
            end

            open("results/$(name)_tacoverse_filter_time.json", "w") do f
                @printf f "%.3g" data["tacotier_filter_time"]
            end

            open("results/$(name)_tacoverse_bench_time.json", "w") do f
                @printf f "%.3g" data["sample_mean_tacoverse_bench"] * 100 * data["tacoverse_length"]
            end

            p = plot(title="Runtime vs. Dimension (Density p=0.01)", xlabel="Dimension n", ylabel="Runtime (Seconds)", xscale=:log10, yscale=:log10, legend=:topleft)
            p = plot!(p, data["n_series"], data["default_n_series"], label="Default Schedule")
            p = plot!(p, data["n_series"], data["auto_n_series"], label="Tuned Schedule")
            savefig(p, "results/$(name)_n_series.png")

            p = plot(title="Runtime vs. Density (Dimension n=10^4)", xlabel="Density p", ylabel="Runtime (Seconds)", xscale=:log10, yscale=:log10, legend=:topleft)
            p = plot!(p, reverse(data["p_series"]), reverse(data["default_p_series"]), label="Default Schedule")
            p = plot!(p, reverse(data["p_series"]), reverse(data["auto_p_series"]), label="Tuned Schedule")
            savefig(p, "results/$(name)_p_series.png")


        end
    end
end

main()