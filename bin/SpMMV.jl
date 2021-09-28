using Pigeon

a = Dense(:a, [:I])
B = Fiber(:B, [[coiter], [coiter]], [:I, :J])
#B = Fiber(:B, [[locate, coiter], [locate, coiter]], [:I, :J])
C = Fiber(:C, [[coiter], [coiter]], [:J, :K])
#C = Fiber(:C, [[locate, coiter], [locate, coiter]], [:J, :K])
d = Dense(:d, [:K])

ex = @i @loop k j i a[i] += B[i, j] * C[j, k] * d[k]

#workspacer(name, dims) = Fiber(name, map(_->[locate, coiter], dims), dims)
workspacer(name, ::Pigeon.Read, dims) = Fiber(name, map(_->[coiter], dims), dims)
workspacer(name, mode, dims) = Fiber(name, map(_->[locate], dims), dims)

schedules = saturate_index(ex, Pigeon.AsymptoticContext, workspacer=workspacer)

schedules = map(Pigeon.concordize, schedules)
schedules = mapreduce(Pigeon.PrewalkSaturate(Pigeon.saturate_formats), vcat, schedules)

#foreach(display, schedules)

println(length(schedules))

#=
a = Dense(:a, [:I])
B = Fiber(:B, [coiter, coiter], [:J, :I])
C = Fiber(:C, [coiter, coiter], [:K, :J])
B.perm = [2,1]
C.perm = [2,1]
d = Dense(:d, [:K])
w = Fiber(:w, [coiter], [:J])
ex = @i @loop k j i ((a[i] += *(B[j, i], w[j])) where (w[j] = *(C[k, j], d[k])))

display(Pigeon.simplify_asymptote(asymptote(ex)))
exit()
=#
#display(Pigeon.supersimplify_asymptote(asymptote(ex)))
#exit()

#=
dimassumes = [
Pigeon.Exists(:i, Pigeon.Predicate(:I, :i)),
Pigeon.Exists(:j, Pigeon.Predicate(:J, :j)),
Pigeon.Exists(:k, Pigeon.Predicate(:K, :k)),
]
=#

frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [a, B, C, d]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

B = Fiber(:B, [locate, coiter], [:K, :I])
C = Fiber(:C, [locate, coiter], [:K, :J])

#display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(@i @loop k j i A[i,j] += B[k, i] * C[k, j])))


foreach(display, frontier)
