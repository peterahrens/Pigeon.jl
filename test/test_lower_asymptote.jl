@testset "asymptote" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists
    using Pigeon: isdominated

    A = Fiber(:A, [locate, locate], [:I, :J])
    B = Fiber(:B, [locate, coiter], [:J, :K])
    C = Fiber(:C, [locate, coiter], [:I, :K])

    a = Pigeon.asymptote(i" ∀ i, j, k A[i, j] += B[j, k] * C[i, k]")
    display(a)
    display(Pigeon.supersimplify_asymptote(a))
    println()
    a_ref = Cup(
        Such(Times(:i, :j, :k), Wedge(
            Predicate(:I, :i),
            Predicate(:J, :j),
            Predicate(:K, :k),
            Predicate(:B, :j, :k)
        )),
        Such(Times(:i, :j, :k), Wedge(
            Predicate(:I, :i),
            Predicate(:J, :j),
            Predicate(:K, :k),
            Predicate(:C, :i, :k)
        )),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    #=
    D = Fiber(:D, [locate])
    E = Fiber(:E, [coiter])
    F = Fiber(:F, [locate])
    a = Pigeon.asymptote(i" ∀ i D[i] += E[i] * F[i]")
    display(a)
    display(Pigeon.supersimplify_asymptote(a))
    println()

    A = Fiber(:A, [locate])
    B = Fiber(:B, [coiter])
    C = Fiber(:C, [coiter])
    D = Fiber(:D, [coiter])
    w = Fiber(:w, [coiter])
    w′ = Fiber(:w, [locate])
    a = Pigeon.asymptote(i"∀ i A[i] += B[i] * w[i] with ∀ i w′[i] += C[i] * D[i]")
    display(a)
    display(Pigeon.supersimplify_asymptote(a))
    println()

    a = Pigeon.asymptote(i"∀ i,j A[i] += B[i] * w[j] with ∀ i w′[i] += C[i] * D[i]")
    display(a)
    display(Pigeon.supersimplify_asymptote(a))
    println()

    A = Fiber(:A, [coiter])
    B = Fiber(:B, [locate, coiter])
    a = Pigeon.asymptote(i"∀ i, j A[j] += B[i, j]")
    display(a)
    display(Pigeon.supersimplify_asymptote(a))
    println()
    =#
end