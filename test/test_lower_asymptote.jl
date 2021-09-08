@testset "asymptote" begin
    A = Fiber(:A, [locate, locate])
    B = Fiber(:B, [locate, coiter])
    C = Fiber(:C, [locate, coiter])

    a = Pigeon.asymptote(i" ∀ i, j, k A[i, j] += B[j, k] * C[i, k]")
    display(a)
    display(Pigeon.simplify_asymptote(a))
    println()

    D = Fiber(:D, [locate])
    E = Fiber(:E, [coiter])
    F = Fiber(:F, [locate])
    a = Pigeon.asymptote(i" ∀ i D[i] += E[i] * F[i]")
    display(a)
    display(Pigeon.simplify_asymptote(a))
    println()

    A = Fiber(:A, [locate])
    B = Fiber(:B, [coiter])
    C = Fiber(:C, [coiter])
    D = Fiber(:D, [coiter])
    w = Fiber(:w, [coiter])
    w′ = Fiber(:w, [locate])
    a = Pigeon.asymptote(i"∀ i A[i] += B[i] * w[i] with ∀ i w′[i] += C[i] * D[i]")
    display(a)
    display(Pigeon.simplify_asymptote(a))
    println()

    a = Pigeon.asymptote(i"∀ i,j A[i] += B[i] * w[j] with ∀ i w′[i] += C[i] * D[i]")
    display(a)
    display(Pigeon.simplify_asymptote(a))
    println()
end