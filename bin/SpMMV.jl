using Pigeon

a = Dense(:a, [:I])
#B = Fiber(:B, [[coiter], [coiter]], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
#C = Fiber(:C, [[coiter], [coiter]], [:J, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[i, j] * C[j, k] * d[k]

#=
B = Fiber(:B, [coiter, coiter], [:I, :J])
C = Fiber(:C, [coiter, coiter], [:J, :K])
w = Fiber(:w, [locate], [:J])
w′ = Fiber(:w, [coiter], [:J])

using Pigeon: Cup, Such, Times, Domain, Wedge, Exists

B = Fiber(:B, [coiter, coiter], [:J, :I], 0, (2, 1), false)

ex = @i ((@loop j i a[i] += *(B[j, i], w′[j])) where (@loop j k w[j] = *(C[j, k], d[k])))
#display(Pigeon.supersimplify_asymptote(Such(Cup(asymptote(ex), map(Pigeon.read_cost, [a, B, C, d])...), Wedge(map(Pigeon.assume_nonempty, [B, C])...))))
display(asymptote(ex))
println()
display(Pigeon.normalize_asymptote(asymptote(ex)))
println()
display(Pigeon.supersimplify_asymptote(asymptote(ex)))
println()

w = Fiber(:w, [], [])
w′ = Fiber(:w, [], [])

ex = @i @loop j ((@loop i a[i] += *(B[j, i], w′[])) where (@loop k w[] = *(C[j, k], d[k])))
#display(Pigeon.supersimplify_asymptote(Such(Cup(asymptote(ex), map(Pigeon.read_cost, [a, B, C, d])...), Wedge(map(Pigeon.assume_nonempty, [B, C])...))))
display(Pigeon.supersimplify_asymptote(asymptote(ex)))
println()

exit()

=#

#workspacer(name, dims) = Fiber(name, map(_->[locate, coiter], dims), dims)
#workspacer(name, ::Pigeon.Read, dims) = Fiber(name, map(_->[locate, coiter], dims), dims)
#workspacer(name, mode, dims) = Fiber(name, map(_->[locate], dims), dims)


#foreach(display, schedules)

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


#frontier = filter_pareto(schedules, sunk_costs = [map(Pigeon.read_cost, [a, B, C, d]); Domain(gensym(), :j)], assumptions=map(Pigeon.assume_nonempty, [B, C]))
frontier = Pigeon.autoschedule(prgm, sunk_costs = map(Pigeon.read_cost, [a, B, C, d]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

#B = Fiber(:B, [locate, coiter], [:K, :I])
#C = Fiber(:C, [locate, coiter], [:K, :J])

#display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(@i @loop k j i A[i,j] += B[k, i] * C[k, j])))

#frontier = filter_pareto(schedules, sunk_costs = map(Pigeon.read_cost, [a, B, C, d]), assumptions=map(Pigeon.assume_nonempty, [B, C]))

foreach(display, frontier)


