using Statistics
using BenchmarkTools
using BSON
using Random
using JSON

using Pigeon: maxdepth, format_workspaces, transform_reformat, MarkInsertContext, concordize, generate_uniform_taco_inputs, maxworkspace, AsymptoticContext, fiber_workspacer, PostwalkSaturate, bigprotocolize, run_taco, noprotocolize, tacoprotocolize, maxinsert, istacoformattable, taco_workspacer, AbstractSymbolicHollowTensor, read_cost, assume_nonempty, defaultprotocolize
using Pigeon: Such, Cup, Wedge, isdominated
using SymbolicUtils: Postwalk

macro hotbelapsed(ex, args...)
    return esc(Expr(:block,
        Expr(:macrocall, Symbol("@belapsed"), __module__, ex, :(seconds=eps()), args...),
        Expr(:macrocall, Symbol("@belapsed"), __module__, ex, args...)
    ))
end

function paper(prgm, args, fname)
    data = Dict()

    _universe = Ref([])
	universe_build_time = @hotbelapsed begin
		universe = saturate_index($prgm)
		universe = filter_pareto(universe, by = kernel -> maxdepth(kernel)) #Filter Step
		universe = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), universe)
		universe = mapreduce(PostwalkSaturate(bigprotocolize), vcat, universe)
	    universe = map(prgm -> transform_reformat(prgm, MarkInsertContext()), universe)
	    universe = map(Pigeon.concordize, universe)
        $_universe[] = universe
	end
    universe = _universe[]

    #println(:universe)
    #foreach(display, universe)

    data["universe_build_time"] = universe_build_time
    data["universe_length"] = length(universe)

    Pigeon.taco_mode[] = true
    _tacoverse = Ref([])
	tacoverse_build_time = @hotbelapsed begin
		tacoverse = saturate_index($prgm)
		tacoverse = filter_pareto(tacoverse, by = kernel -> maxdepth(kernel)) #Filter Step
		tacoverse = filter(kernel -> maxworkspace(kernel) <= 1, tacoverse) #TACO restriction
		tacoverse = map(prgm->format_workspaces(prgm, AsymptoticContext, taco_workspacer), tacoverse)
		tacoverse = map(Postwalk(noprotocolize), tacoverse)
	    tacoverse = map(Pigeon.concordize, tacoverse)
		tacoverse = mapreduce(PostwalkSaturate(tacoprotocolize), vcat, tacoverse)
	    tacoverse = map(prgm -> transform_reformat(prgm, MarkInsertContext()), tacoverse)
		tacoverse = filter(kernel -> maxinsert(kernel) <= 1, tacoverse) #TACO restriction
		tacoverse = filter(kernel -> istacoformattable(transform_reformat(kernel)), tacoverse)
        $_tacoverse[] = tacoverse
	end
    tacoverse = _tacoverse[]
    Pigeon.taco_mode[] = false

    #println(:tacoverse)
    #foreach(display, tacoverse)

    data["tacoverse_build_time"] = tacoverse_build_time
    data["tacoverse_length"] = length(tacoverse)

    Pigeon.taco_mode[] = true
    #sample_mean_tacoverse_bench = mean(map(tacoverse[randperm(end)[1:min(end, 100)]]) do kernel
    sample_mean_tacoverse_bench = mean(map(tacoverse[randperm(end)[1:min(end, 5)]]) do kernel
        kernel = transform_reformat(kernel)
        inputs = Pigeon.generate_uniform_taco_inputs(args, 1_000, 0.01)
        run_taco(kernel, inputs)
    end)
    Pigeon.taco_mode[] = false

    data["sample_mean_tacoverse_bench"] = sample_mean_tacoverse_bench

    _frontier = Ref([])
    frontier_filter_time = @hotbelapsed begin
        sunk_costs = map(read_cost, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))
        assumptions = map(assume_nonempty, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))

        $_frontier[] = filter_pareto($universe, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end
    frontier = _frontier[]

    data["frontier_filter_time"] = frontier_filter_time
    data["frontier_length"] = length(frontier)

    _tacotier = Ref([])
    tacotier_filter_time = @hotbelapsed begin
        sunk_costs = map(read_cost, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))
        assumptions = map(assume_nonempty, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))

        $_tacotier[] = filter_pareto($tacoverse, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end
    tacotier = _tacotier[]

    #println(:tacotier)
    #foreach(display, tacotier)

    data["tacotier_filter_time"] = tacotier_filter_time
    data["tacotier_length"] = length(tacotier)

    Pigeon.taco_mode[] = true
    tacotier_inputs = Pigeon.generate_uniform_taco_inputs(args, 1_000, 0.01)
    tacotier_bench = map(tacotier) do kernel
        kernel = transform_reformat(kernel)
        run_taco(kernel, tacotier_inputs)
    end
    data["tacotier_bench"] = tacotier_bench

    auto_kernel = transform_reformat(tacotier[findmin(tacotier_bench)[2]])
    Pigeon.taco_mode[] = false

    default_kernel = Postwalk(noprotocolize)(prgm)
    default_kernel = Postwalk(defaultprotocolize)(default_kernel)
    default_kernel = transform_reformat(default_kernel, MarkInsertContext())
    default_kernel = concordize(default_kernel)
    Pigeon.taco_mode[] = true
    default_kernel = transform_reformat(default_kernel)
    Pigeon.taco_mode[] = false 

    default_kernel_bench = run_taco(default_kernel, Pigeon.generate_uniform_taco_inputs(args, 1_000, 0.01))

    data["default_kernel_bench"] = default_kernel_bench

    println(JSON.json(data, 2))

    open("$fname.json", "w") do f print(f, JSON.json(data, 2)) end

    n_series = 10 .^ (1:4)
    default_n_series = []
    auto_n_series = []
    for n = n_series
        println(n)
        input = Pigeon.generate_uniform_taco_inputs(args, n, 0.01)
        push!(default_n_series, run_taco(default_kernel, input))
        push!(auto_n_series, run_taco(auto_kernel, input))
    end

    data["n_series"] = n_series
    data["default_n_series"] = default_n_series
    data["auto_n_series"] = auto_n_series

    p_series = 0.1 .^ 0:4
    default_p_series = []
    auto_p_series = []
    for p = p_series
        println(p)
        input = Pigeon.generate_uniform_taco_inputs(args, 1_000, p)
        push!(default_p_series, run_taco(default_kernel, input))
        push!(auto_p_series, run_taco(auto_kernel, input))
    end

    data["p_series"] = p_series
    data["default_p_series"] = default_p_series
    data["auto_p_series"] = auto_p_series

    open("$fname.json", "w") do f print(f, JSON.json(data, 2)) end
end