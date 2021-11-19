using Pigeon

using Statistics
using BenchmarkTools
using BSON
using Random
using JSON

using Pigeon: maxdepth, format_workspaces, transform_reformat, MarkInsertContext, concordize, generate_uniform_taco_inputs, maxworkspace, AsymptoticContext, fiber_workspacer, PostwalkSaturate, bigprotocolize, run_taco, noprotocolize, tacoprotocolize, maxinsert, istacoformattable, taco_workspacer, AbstractSymbolicHollowTensor, read_cost, assume_nonempty, defaultprotocolize
using Pigeon: Such, Cup, Wedge, isdominated, Domain
using SymbolicUtils: Postwalk
#BenchmarkTools.DEFAULT_PARAMETERS.seconds = 10

function paper(prgm, args, dims, fname)
    data = Dict()
    bin = Dict()

    _universe = Ref([])
	universe_build_time = @belapsed begin
        @info "build universe"
		universe = saturate_index($prgm)
        @info "filter depth"
		universe = filter_pareto(universe, by = kernel -> maxdepth(kernel)) #Filter Step
        @info "workspace"
		universe = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), universe)
        @info "protocolize"
		universe = mapreduce(PostwalkSaturate(bigprotocolize), vcat, universe)
        $_universe[] = universe
	end
    universe = _universe[]

    #println(:universe)
    #foreach(display, universe)

    data["universe_build_time"] = universe_build_time
    data["universe_length"] = length(universe)

    println(data)
end

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat(), ListFormat()], [:I, :K, :L])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:K, :J])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:L, :J])

prgm = @i @loop i j k l A[i, j] += B[i, k, l] * C[k, j] * D[l, j]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "smttkrp")
