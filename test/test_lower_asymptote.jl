@testset "asymptote" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists
    using Pigeon: isdominated

    #SDMMM tests
    A = Dense(:A, [:I, :J])
    B = Fiber(:B, [coiter, coiter], [:I, :J])
    w = Fiber(:w, [], [])
    C = Dense(:C, [:I, :K])
    D = Dense(:D, [:J, :K])

    a = Pigeon.asymptote(@i (
        @loop i j (
            (
                A[i, j] += *(w[], B[i, j])
            ) where (
                @loop k (
                    w[] += *(C[i, k], D[j, k])
                )
            )
        )
    ))

    a_ref = Such(
                Times(
                    Domain(:i, :I),
                    Domain(:j, :J),
                    Domain(:k, :K)
                ),
                Wedge(Predicate(:B, :i, :j))
            )
    @test Pigeon.asymptote_equal(a, a_ref)

    D = Fiber(:D, [locate], [:I])
    E = Fiber(:E, [coiter], [:I])
    F = Fiber(:F, [locate], [:I])
    a = Pigeon.asymptote(@i @loop i D[i] += E[i] * F[i])
    a_ref = Such(
        Times(Domain(:i, :I)),
        Wedge(
            Predicate(:E, :i)
        )
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
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:C, :i)
            )
        ),
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:D, :i)
            )
        ),
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:B, :i)
            )
        ),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    a = Pigeon.asymptote(@i (@loop i j A[i] += B[i] * w[j]) where (@loop i w′[i] += C[i] * D[i]))
    a_ref = Cup(
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:C, :i)
            )
        ),
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:D, :i)
            )
        ),
        Such(
            Times(Domain(:i, :I)),
            Wedge(
                Predicate(:B, :i)
            )
        ),
        Such(
            Times(Domain(:i, :I), Domain(:j, :I)),
            Wedge(
                Predicate(:B, :i),
                Predicate(:C, :j),
                Predicate(:D, :j)
            )
        ),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    A = Fiber(:A, [coiter], [:J])
    B = Fiber(:B, [locate, coiter], [:I, :J])
    a = Pigeon.asymptote(@i @loop i j A[j] += B[i, j])

    a_ref = Cup(
        Domain(:i, :I),
        Such(Times(Domain(:i, :I), Domain(:j, :J)),
            Wedge(
                Predicate(:A, :j),
            )
        ),
        Such(Times(Domain(:i, :I), Domain(:j, :J)),
            Wedge(
                Exists(:i, Predicate(:B, :i, :j)),
            )
        ),
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    A = Fiber(:A, [locate, locate], [:I, :J])
    B = Fiber(:B, [locate, coiter], [:J, :K])
    C = Fiber(:C, [locate, coiter], [:I, :K])

    a = Pigeon.asymptote(@i @loop i j k A[i, j] += B[j, k] * C[i, k])
    a_ref = Cup(
        Times(Domain(:i, :I), Domain(:j, :J)),
        Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K)),
            Wedge(
                Predicate(:B, :j, :k)
            )
        ),
        Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K)),
            Wedge(
                Predicate(:C, :i, :k)
            )
        ),
    )

    @test Pigeon.asymptote_equal(a, a_ref)

    A = Fiber(:A, [locate, locate], [:I, :J])
    B = Fiber(:B, [coiter, coiter], [:K, :J])
    C = Fiber(:C, [coiter, coiter], [:K, :I])

    a = Pigeon.asymptote(@i @loop k i j A[i, j] += B[k, j] * C[k, i])
    a_ref = Cup(
        Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K)),
            Wedge(Predicate(:B, :k, :j), Predicate(:C, :k, :i))
        ),
        Such(Times(Domain(:k, :K)),
            Exists(:j_1, Predicate(:B, :k, :j_1))
        ),
        Such(Times(Domain(:k, :K)),
            Exists(:i_1, Predicate(:C, :k, :i_1))
        ),
    )
    @test Pigeon.asymptote_equal(a, a_ref)
end