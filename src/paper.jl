using Statistics
using BenchmarkTools
function paper(prgm, name)
	#; sunk_costs = [], assumptions = [], protocolize = bigprotocolize)
    universe = []
	universe_build_time = @btime begin
		universe = saturate_index(prgm)
		universe = filter_pareto(universe, by = kernel -> maxdepth(kernel))
		universe = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), universe)
		universe = mapreduce(PostwalkSaturate(bigprotocolize), vcat, universe)
	    universe = map(prgm -> transform_reformat(prgm, MarkInsertContext()), universe)
	    universe = map(Pigeon.concordize, universe)
	end

    sample_mean_universe_bench = mean(map(universe[randperm(end)[1:100]]) do kernel
        kernel = transform_reformat(kernel)
        run_taco(kernel, test_inputs(kernel, n=1_000_000, ρ=0.01)...)
    end)

    tacoverse = []
	tacoverse_filter_time = @btime begin
        tacoverse = filter(kernel->maxworkspace(kernel) <= 1, universe)
    end

    frontier_filter_time = @btime begin
        sunk_costs = map(read_cost, sparseglobals(prgm))
        assumptions = map(assume_nonempty, sparseglobals(prgm))

        frontier = filter_pareto(universe, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end

    final_frontier_inputs = test_inputs(kernel, n=1_000_000, ρ=0.01)
    frontier_bench = map(frontier) do kernel
        kernel = transform_reformat(kernel)
        run_taco(kernel, final_frontier_inputs...)
    end

    auto_kernel = frontier[findmin(frontier_bench)]

    default_kernel = Postwalk(defaultprotocolize)(prgm)
    default_kernel = transform_reformat(default_kernel, MarkInsertContext())
    default_kernel = concordize(default_kernel)
    default_kernel = transform_reformat(default_kernel)

    default_kernel_bench = run_taco(default_kernel, test_inputs(default_kernel, n=1_000_000, ρ=0.01)...)
end