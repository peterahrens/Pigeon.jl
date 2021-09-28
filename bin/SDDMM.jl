using Pigeon

A = Dense(:A, [:I, :J])
B = Fiber(:B, [[locate, coiter], [locate, coiter]], [:I, :J])
C = Dense(:C, [:I, :K])
D = Dense(:D, [:K, :J])

ex = @i @loop k j i A[i, j] += B[i, j] * C[i, k] * D[k, j]

#workspacer(name, dims) = Fiber(name, map(_->[locate, coiter], dims), dims)
workspacer(name, ::Pigeon.Read, dims) = Fiber(name, map(_->[coiter], dims), dims)
workspacer(name, mode, dims) = Fiber(name, map(_->[locate], dims), dims)

schedules = saturate_index(ex, Pigeon.AsymptoticContext, workspacer=workspacer)

schedules = map(Pigeon.concordize, schedules)
schedules = mapreduce(Pigeon.PrewalkSaturate(Pigeon.saturate_formats), vcat, schedules)

#foreach(display, schedules)

println(length(schedules))

#frontier = filter_pareto(schedules)
frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [B]), assumptions=map(Pigeon.assume_nonempty, [B,]))

foreach(display, frontier)
