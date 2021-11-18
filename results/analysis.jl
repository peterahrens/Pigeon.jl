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
        "mttkrp",
        "smttkrp",
    ]
    rpath = "/Users/Peter/Projects/pldi2022/results"
    if !isdir(rpath)
        println("No output directory")
        exit()
    end

    for name in names
        if isfile("$(name)_data.json")
            data = Dict()
            open("$(name)_data.json", "r") do f
                data = JSON.parse(f)
            end
            open(joinpath(rpath, "$(name)_N.json"), "w") do f
                @printf f "%.6g" data["N"]
            end
            if haskey(data, "frontier_length")
                open(joinpath(rpath, "$(name)_frontier_length.json"), "w") do f
                    @printf f "%.6g" data["frontier_length"]
                end
            end
            if haskey(data, "universe_length")
                open(joinpath(rpath, "$(name)_universe_length.json"), "w") do f
                    @printf f "%.6g" data["universe_length"]
                end
            end
            open(joinpath(rpath, "$(name)_tacotier_length.json"), "w") do f
                @printf f "%.6g" data["tacotier_length"]
            end
            open(joinpath(rpath, "$(name)_tacoverse_length.json"), "w") do f
                @printf f "%.6g" data["tacoverse_length"]
            end

            open(joinpath(rpath, "$(name)_tacoverse_filter_time.json"), "w") do f
                @printf f "%.6g" data["tacotier_filter_time"]
            end

            open(joinpath(rpath, "$(name)_tacoverse_bench_time.json"), "w") do f
                @printf f "%.6g" data["sample_mean_tacoverse_bench"] * 100 * data["tacoverse_length"]
            end

            open(joinpath(rpath, "$(name)_tacoverse_mean_filter_time.json"), "w") do f
                @printf f "%.3g" data["tacotier_filter_time"] / data["tacoverse_length"]
            end

            p = plot(title="Runtime vs. Dimension (p=0.01)", xlabel="Dimension n", ylabel="Runtime (Seconds)", xscale=:log10, yscale=:log10, legend=:topleft, titlefontsize=12, thickness_scaling=1.5)
            p = plot!(p, data["n_series"], data["default_n_series"], label="Default Schedule", markershape=:circle)
            p = plot!(p, data["n_series"], data["auto_n_series"], label="Tuned Schedule", markershape=:circle)
            savefig(p, joinpath(rpath, "$(name)_n_series.png"))

            p = plot(title="Runtime vs. Density (n=$(data["N"]))", xlabel="Density p", ylabel="Runtime (Seconds)", xscale=:log10, yscale=:log10, legend=:topleft, titlefontsize=12, thickness_scaling=1.5, xflip=false)
            p = plot!(p, data["p_series"], data["default_p_series"], label="Default Schedule", markershape=:circle)
            p = plot!(p, data["p_series"], data["auto_p_series"], label="Tuned Schedule", markershape=:circle)
            savefig(p, joinpath(rpath, "$(name)_p_series.png"))
        end
    end
end

main()