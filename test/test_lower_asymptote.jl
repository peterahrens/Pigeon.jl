@testset "asymptote" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists
    using Pigeon: isdominated

    A = Fiber(:A, [locate, locate], [:I, :J])
    B = Fiber(:B, [locate, coiter], [:J, :K])
    C = Fiber(:C, [locate, coiter], [:I, :K])

    a = Pigeon.asymptote(@i @loop i j k A[i, j] += B[j, k] * C[i, k])
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
    display(Pigeon.simplify_asymptote(a))
    println()
    @test Pigeon.asymptote_equal(a, a_ref)

    D = Fiber(:D, [locate], [:I])
    E = Fiber(:E, [coiter], [:I])
    F = Fiber(:F, [locate], [:I])
    a = Pigeon.asymptote(@i @loop i D[i] += E[i] * F[i])
    a_ref = Cup(
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:E, :i)
        )),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    A = Fiber(:A, [locate], [:I])
    B = Fiber(:B, [coiter], [:I])
    C = Fiber(:C, [coiter], [:I])
    D = Fiber(:D, [coiter], [:I])
    w = Fiber(:w, [coiter], [:I])
    w′ = Fiber(:w, [locate], [:I])
    a = Pigeon.asymptote(@i (@loop i A[i] += B[i] * w[i]) where (@loop j w′[j] += C[j] * D[j]))
    a_ref = Cup(
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:C, :i)
        )),
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:D, :i)
        )),
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:B, :i)
        )),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    a = Pigeon.asymptote(@i (@loop i j A[i] += B[i] * w[j]) where (@loop i w′[i] += C[i] * D[i]))
    a_ref = Cup(
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:C, :i)
        )),
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:D, :i)
        )),
        Such(Times(:i), Wedge(
            Predicate(:I, :i),
            Predicate(:B, :i)
        )),
        Such(Times(:i, :j), Wedge(
            Predicate(:I, :i),
            Predicate(:I, :j),
            Predicate(:B, :i),
            Predicate(:C, :j),
            Predicate(:D, :j),
        )),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    A = Fiber(:A, [coiter], [:J])
    B = Fiber(:B, [locate, coiter], [:I, :J])
    a = Pigeon.asymptote(@i @loop i j A[j] += B[i, j])

    a_ref = Cup(
        Such(Times(:i, :j), Wedge(
            Predicate(:I, :i),
            Predicate(:J, :j),
            Predicate(:A, :j),
        )),
        Such(Times(:i, :j), Wedge(
            Predicate(:I, :i),
            Predicate(:J, :j),
            Exists(:i, Predicate(:B, :i, :j)),
        )),
    )
    @test Pigeon.asymptote_equal(a, a_ref)
end