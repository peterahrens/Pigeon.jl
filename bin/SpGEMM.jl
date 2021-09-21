using Pigeon

A = Fiber(:A, [[locate], [locate]], [:I, :J])
B = Fiber(:B, [[locate, coiter], [locate, coiter]], [:K, :I])
C = Fiber(:C, [[locate, coiter], [locate, coiter]], [:K, :J])

ex = @i @loop k j i A[i,j] += B[k, i] * C[k, j]

schedules = saturate_index(ex)

schedules = map(Pigeon.concordize, schedules)
schedules = mapreduce(Pigeon.PrewalkStep(Pigeon.saturate_formats), vcat, schedules)

#=
dimassumes = [
Pigeon.Exists(:i, Pigeon.Predicate(:I, :i)),
Pigeon.Exists(:j, Pigeon.Predicate(:J, :j)),
Pigeon.Exists(:k, Pigeon.Predicate(:K, :k)),
]
=#

#frontier = filter_pareto(schedules)
frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [Fiber(:C, [coiter, coiter], [:K, :J]), Fiber(:B, [coiter, coiter], [:K, :I])]))#, assumptions=[map(Pigeon.assume_nonempty, [B, C])..., dimassumes...])
#frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [Fiber(:C, [coiter, coiter], [:K, :J]), Fiber(:B, [coiter, coiter], [:K, :I])]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

B = Fiber(:B, [locate, coiter], [:K, :I])
C = Fiber(:C, [locate, coiter], [:K, :J])

#display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(@i @loop k j i A[i,j] += B[k, i] * C[k, j])))


foreach(display, frontier)
