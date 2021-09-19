using Pigeon

A = Fiber(:A, [locate, locate], [:I, :J])
B = Fiber(:B, [coiter, coiter], [:K, :I])
C = Fiber(:C, [coiter, coiter], [:K, :J])

ex = i"∀ k, j, i A[i,j] += B[k, i] * C[k, j]"

schedules = saturate_index(ex)

dimassumes = [
Pigeon.Exists(:i, Pigeon.Predicate(:I, :i)),
Pigeon.Exists(:j, Pigeon.Predicate(:J, :j)),
Pigeon.Exists(:k, Pigeon.Predicate(:K, :k)),
]

frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [B, C]), assumptions=[map(Pigeon.assume_nonempty, [B, C])..., dimassumes...])

foreach(display, frontier)
