@testset "asymptote" begin
    A = Fiber(:A, [locate, coiter])
    B = Fiber(:B, [coiter, locate])
    C = Fiber(:C, [locate, coiter])

    a = Pigeon.asymptote(i" ∀ i, j, k A[i, j] += B[j, k] * C[k, i]")
    display(a)
    display(Pigeon.simplify_asymptote(a))
    println()
end