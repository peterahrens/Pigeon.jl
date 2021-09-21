using Pigeon

A = Fiber(:A, [locate, locate], [:I, :J])
B = Fiber(:B, [locate, coiter], [:K, :I])
C = Fiber(:C, [locate, coiter], [:K, :J])

ex = @i @loop k j i A[i,j] += B[k, i] * C[k, j]

schedules = saturate_index(ex)

dimassumes = [
Pigeon.Exists(:i, Pigeon.Predicate(:I, :i)),
Pigeon.Exists(:j, Pigeon.Predicate(:J, :j)),
Pigeon.Exists(:k, Pigeon.Predicate(:K, :k)),
]

frontier = filter_pareto(schedules)
#frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [B, C]), assumptions=[map(Pigeon.assume_nonempty, [B, C])..., dimassumes...])

foreach(display, frontier)
