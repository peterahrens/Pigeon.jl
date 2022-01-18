using Statistics
using BenchmarkTools
using BSON
using Random
using JSON

using Pigeon: maxdepth, format_workspaces, transform_reformat, MarkInsertContext, concordize, generate_uniform_taco_inputs, maxworkspace, AsymptoticContext, fiber_workspacer, PostwalkExpand, bigprotocolize, run_taco, noprotocolize, tacoprotocolize, maxinsert, istacoformattable, taco_workspacer, AbstractSymbolicHollowTensor, read_cost, assume_nonempty, defaultprotocolize
using Pigeon: Such, Cup, Wedge, isdominated, Domain
using RewriteTools: PostwalkRewrite
#BenchmarkTools.DEFAULT_PARAMETERS.seconds = 10

function paper(prgm, args, dims, fname)
    data = Dict()
    bin = Dict()

    @info "kernel" fname

    default_kernel = SomeRewrite(PostwalkRewrite(noprotocolize))(prgm)
    default_kernel = SomeRewrite(PostwalkRewrite(defaultprotocolize))(default_kernel)
    default_kernel = transform_reformat(default_kernel, MarkInsertContext())
    default_kernel = concordize(default_kernel)
    Pigeon.taco_mode[] = true
    default_kernel = transform_reformat(default_kernel)
    Pigeon.taco_mode[] = false

    bin["default_kernel"] = default_kernel

    N = 8
    n_series = []
    while true
        input = Pigeon.generate_uniform_taco_inputs(args, N, 0.01)
        t = run_taco(default_kernel, input)
        @info "sizing up kernel" N t
        if t < 1 && N < 10_000
            push!(n_series, N)
            N *= 2
        else
            break
        end
    end

    data["N"] = N

    Pigeon.taco_mode[] = true
    _tacoverse = Ref([])
	tacoverse_build_time = @belapsed begin
        @info "building universe"
		tacoverse = saturate_index($prgm)
        @info "filtering universe"
		tacoverse = filter_pareto(tacoverse, by = kernel -> maxdepth(kernel)) #Filter Step
        @info "restricting workspace dims"
		tacoverse = filter(kernel -> maxworkspace(kernel) <= 1, tacoverse) #TACO restriction
        @info "formating for taco"
		tacoverse = map(prgm->format_workspaces(prgm, AsymptoticContext, taco_workspacer), tacoverse)
        @info "protocolizing"
		tacoverse = map(SomeRewrite(PostwalkRewrite(noprotocolize)), tacoverse)
        @info "concordizing"
	    tacoverse = map(Pigeon.concordize, tacoverse)
        @info "protocolizing again"
		tacoverse = mapreduce(SomeExpand(PostwalkExpand(tacoprotocolize)), vcat, tacoverse)
        @info "marking inserts"
	    tacoverse = map(prgm -> transform_reformat(prgm, MarkInsertContext()), tacoverse)
        @info "filtering overinserts"
		tacoverse = filter(kernel -> maxinsert(kernel) <= 1, tacoverse) #TACO restriction
        @info "filtering taco-compatible"
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
    sample_mean_tacoverse_bench = mean(map(tacoverse[randperm(end)[1:min(end, 100)]]) do kernel
        @info "benchmark tacoverse" min(length(tacoverse), 100)
        kernel = transform_reformat(kernel)
        inputs = Pigeon.generate_uniform_taco_inputs(args, N, 0.01)
        run_taco(kernel, inputs)
    end)
    Pigeon.taco_mode[] = false

    data["sample_mean_tacoverse_bench"] = sample_mean_tacoverse_bench

    _tacotier = Ref([])
    tacotier_filter_time = @belapsed begin
        @info "filter tacotier"
        dim_costs = map(dim-> Domain(gensym(), dim), $dims)
        sunk_costs = map(read_cost, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))
        assumptions = map(assume_nonempty, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))

        $_tacotier[] = filter_pareto($tacoverse, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs..., dim_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end
    tacotier = _tacotier[]

    bin["tacotier"] = tacotier

    #println(:tacotier)
    #foreach(display, tacotier)

    data["tacotier_filter_time"] = tacotier_filter_time
    data["tacotier_length"] = length(tacotier)

    Pigeon.taco_mode[] = true
    tacotier_inputs = Pigeon.generate_uniform_taco_inputs(args, N, 0.01)
    tacotier_bench = map(tacotier) do kernel
        @info "benchmark tacotier" length(tacotier)
        kernel = transform_reformat(kernel)
        run_taco(kernel, tacotier_inputs)
    end
    data["tacotier_bench"] = tacotier_bench

    auto_kernel = transform_reformat(tacotier[findmin(tacotier_bench)[2]])
    Pigeon.taco_mode[] = false
    bin["auto_kernel"] = auto_kernel

    default_kernel_bench = run_taco(default_kernel, tacotier_inputs)

    data["default_kernel_bench"] = default_kernel_bench

    default_n_series = []
    auto_n_series = []
    for n = n_series
        @info "n_series" n n_series[end]
        input = Pigeon.generate_uniform_taco_inputs(args, n, 0.01)
        push!(default_n_series, run_taco(default_kernel, input))
        push!(auto_n_series, run_taco(auto_kernel, input))
    end

    data["n_series"] = n_series
    data["default_n_series"] = default_n_series
    data["auto_n_series"] = auto_n_series

    p_series = 0.5 .^ (6:16)
    default_p_series = []
    auto_p_series = []
    for p = p_series
        @info "p_series" p p_series[end]
        input = Pigeon.generate_uniform_taco_inputs(args, N, p)
        push!(default_p_series, run_taco(default_kernel, input))
        push!(auto_p_series, run_taco(auto_kernel, input))
    end

    data["p_series"] = p_series
    data["default_p_series"] = default_p_series
    data["auto_p_series"] = auto_p_series

    open("$(fname)_data.json", "w") do f print(f, JSON.json(data, 2)) end
    BSON.bson("$(fname)_bin.bson", bin)

    _universe = Ref([])
	universe_build_time = @belapsed begin
        @info "build universe"
		universe = saturate_index($prgm)
        @info "filter depth"
		universe = filter_pareto(universe, by = kernel -> maxdepth(kernel)) #Filter Step
        @info "workspace"
		universe = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), universe)
        @info "protocolize"
		universe = mapreduce(SomeExpand(PostwalkExpand(bigprotocolize)), vcat, universe)
        @info "mark insert"
	    universe = map(prgm -> transform_reformat(prgm, MarkInsertContext()), universe)
        @info "concordize"
	    universe = map(Pigeon.concordize, universe)
        $_universe[] = universe
	end
    universe = _universe[]

    #println(:universe)
    #foreach(display, universe)

    data["universe_build_time"] = universe_build_time
    data["universe_length"] = length(universe)

    _frontier = Ref([])
    frontier_filter_time = @belapsed begin
        @info "filter frontier"
        dim_costs = map(dim-> Domain(gensym(), dim), $dims)
        sunk_costs = map(read_cost, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))
        assumptions = map(assume_nonempty, filter(arg->arg isa AbstractSymbolicHollowTensor, $args))

        $_frontier[] = filter_pareto($universe, 
            by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs..., dim_costs...), Wedge(assumptions...))),
            lt = (a, b) -> isdominated(a, b, normal = true)
        )
    end
    frontier = _frontier[]

    data["frontier_filter_time"] = frontier_filter_time
    data["frontier_length"] = length(frontier)
    bin["frontier"] = frontier

    open("$(fname)_data.json", "w") do f print(f, JSON.json(data, 2)) end
    BSON.bson("$(fname)_bin.bson", bin)
end
