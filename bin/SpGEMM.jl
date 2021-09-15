using Pigeon

A = Fiber(:A, [locate, locate], [:I, :J])
B = Fiber(:B, [coiter, coiter], [:I, :K])
C = Fiber(:C, [coiter, coiter], [:K, :J])

ex = i"∀ k, j, i A[i,j] += B[i, k] * C[k, j]"

display(asymptote(ex))
display(simplify_asymptote(asymptote(ex)))

#=
schedules = saturate_index(ex)

frontier = filter_pareto(schedules)

foreach(display, frontier)
=#