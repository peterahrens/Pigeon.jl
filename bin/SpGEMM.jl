using Pigeon

A = Fiber(:A, [[locate], [locate]], [:I, :J])
B = Fiber(:B, [[locate, coiter], [locate, coiter]], [:K, :I])
C = Fiber(:C, [[locate, coiter], [locate, coiter]], [:K, :J])

ex = @i @loop k j i A[i,j] += B[k, i] * C[k, j]

schedules = saturate_index(ex, Pigeon.AsymptoticContext)

schedules = map(Pigeon.concordize, schedules)
schedules = mapreduce(Pigeon.PrewalkSaturate(Pigeon.saturate_formats), vcat, schedules)

frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [B, C]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

B = Fiber(:B, [locate, coiter], [:K, :I])
C = Fiber(:C, [locate, coiter], [:K, :J])

#display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(@i @loop k j i A[i,j] += B[k, i] * C[k, j])))


foreach(display, frontier)
