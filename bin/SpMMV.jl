using Pigeon

a = Dense(:a, [:I])
B = Fiber(:B, [[coiter], [coiter]], [:I, :J])
#B = Fiber(:B, [[locate, coiter], [locate, coiter]], [:I, :J])
C = Fiber(:C, [[coiter], [coiter]], [:J, :K])
#C = Fiber(:C, [[locate, coiter], [locate, coiter]], [:J, :K])
d = Dense(:d, [:K])

ex = @i @loop k j i a[i] += B[i, j] * C[j, k] * d[k]

#workspacer(name, dims) = Fiber(Pigeon.getname(name), map(_->[locate, coiter], dims), dims)
workspacer(name, dims) = Fiber(Pigeon.getname(name), map(_->[coiter], dims), dims)

schedules = saturate_index(ex, Pigeon.AsymptoticContext, workspacer=workspacer)


schedules = map(prg->(display(prg); Pigeon.concordize), schedules)
schedules = mapreduce(Pigeon.PrewalkStep(Pigeon.saturate_formats), vcat, schedules)

display(length(schedules))

#=
dimassumes = [
Pigeon.Exists(:i, Pigeon.Predicate(:I, :i)),
Pigeon.Exists(:j, Pigeon.Predicate(:J, :j)),
Pigeon.Exists(:k, Pigeon.Predicate(:K, :k)),
]
=#

#frontier = filter_pareto(schedules)
#frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [Fiber(:C, [coiter, coiter], [:K, :J]), Fiber(:B, [coiter, coiter], [:K, :I])]))#, assumptions=[map(Pigeon.assume_nonempty, [B, C])..., dimassumes...])
frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [Fiber(:B, [coiter, coiter], [:K, :J]), Fiber(:C, [coiter, coiter], [:K, :I])]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

B = Fiber(:B, [locate, coiter], [:K, :I])
C = Fiber(:C, [locate, coiter], [:K, :J])

#display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(@i @loop k j i A[i,j] += B[k, i] * C[k, j])))


foreach(display, frontier)
