using Statistics
using BenchmarkTools
using BSON
using Random

using Pigeon: maxdepth, format_workspaces, transform_reformat, MarkInsertContext, concordize, generate_uniform_taco_inputs, maxworkspace, AsymptoticContext, fiber_workspacer, PostwalkSaturate, bigprotocolize, run_taco


function paper(point, prgm, args, fname)
    data = Dict()

    _universe = Ref([])
	universe_build_time = @btime begin
		universe = saturate_index(prgm)
		universe = filter_pareto(universe, by = kernel -> maxdepth(kernel))
		universe = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), universe)
		universe = mapreduce(PostwalkSaturate(bigprotocolize), vcat, universe)
	    universe = map(prgm -> transform_reformat(prgm, MarkInsertContext()), universe)
	    universe = map(Pigeon.concordize, universe)
        $_universe[] = universe
	end
    universe = _universe[]

    data["universe_build_time"] = universe_build_time
    data["universe_length"] = length(universe)

    sample_mean_universe_bench = mean(map(universe[randperm(end)[1:min(end, 100)]]) do kernel
        kernel = transform_reformat(kernel)
        inputs = Pigeon.generate_uniform_taco_inputs(args, 1000, 0.1)
        run_taco(point, kernel, inputs)
    end)

    data["sample_mean_universe_bench"] = sample_mean_universe_bench

    tacoverse = []
	tacoverse_filter_time = @btime begin
        tacoverse = filter(kernel->maxworkspace(kernel) <= 1, universe)
    end

    data["tacoverse_filter_time"] = tacoverse_build_time
    data["tacoverse_length"] = length(tacoverse)

    frontier_filter_time = @btime begin
        sunk_costs = map(read_cost, filter(arg->arg isa AbstractSymbolicHollowTensor, args))
        assumptions = map(assume_nonempty, filter(arg->arg isa AbstractSymbolicHollowTensor, args))

        frontier = filter_pareto(universe, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end

    data["frontier_filter_time"] = frontier_filter_time
    data["frontier_length"] = length(frontier)

    println(data)

    #=
    final_frontier_inputs = test_inputs(kernel, n=1_000_000, ρ=0.01)
    frontier_bench = map(frontier) do kernel
        kernel = transform_reformat(kernel)
        run_taco(point, kernel, final_frontier_inputs...)
    end

    auto_kernel = frontier[findmin(frontier_bench)]

    default_kernel = Postwalk(defaultprotocolize)(prgm)
    default_kernel = transform_reformat(default_kernel, MarkInsertContext())
    default_kernel = concordize(default_kernel)
    default_kernel = transform_reformat(default_kernel)

    default_kernel_bench = run_taco(point, default_kernel, test_inputs(default_kernel, n=1_000_000, ρ=0.01)...)
    =#
end