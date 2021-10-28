@testset "asymptote" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists
    using Pigeon: isdominated
    using Pigeon: ListFormat, ArrayFormat, HashFormat
    using Pigeon: StepProtocol, LocateProtocol, AppendProtocol, InsertProtocol

    using Pigeon: Direct

    A = Dense(:A, [:I, :J])
    B = Direct(Fiber(:B, [ListFormat(), ListFormat()], [:I, :J]), [StepProtocol(), StepProtocol()])
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

    D = Direct(Fiber(:D, [ArrayFormat()], [:I]), [LocateProtocol()])
    E = Direct(Fiber(:E, [ListFormat()], [:I]), [StepProtocol()])
    F = Direct(Fiber(:F, [ArrayFormat()], [:I]), [LocateProtocol()])
    a = Pigeon.asymptote(@i @loop i D[i] += E[i] * F[i])
    a_ref = Such(
        Times(Domain(:i, :I)),
        Wedge(
            Predicate(:E, :i)
        )
    )
    @test Pigeon.asymptote_equal(a, a_ref)

    A = Direct(Fiber(:A, [ArrayFormat()], [:I]), [InsertProtocol()])
    B = Direct(Fiber(:B, [ListFormat()], [:I]), [StepProtocol()])
    C = Direct(Fiber(:C, [ListFormat()], [:I]), [StepProtocol()])
    D = Direct(Fiber(:D, [ListFormat()], [:I]), [StepProtocol()])
    w = Fiber(:w, [HashFormat()], [:I])
    w_r = Direct(w, [StepProtocol()])
    w_w = Direct(w, [AppendProtocol()])
    a = Pigeon.asymptote(@i (@loop i A[i] += B[i] * w_r[i]) where (@loop j w_w[j] += C[j] * D[j]))
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

    a = Pigeon.asymptote(@i (@loop i j A[i] += B[i] * w_r[j]) where (@loop i w_w[i] += C[i] * D[i]))
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

    #=
    A = Direct(Fiber(:A, [HashFormat()], [:J]), [InsertProtocol()])
    B = Direct(Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J]), [LocateProtocol(), StepProtocol()])
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
    =#

    A = Direct(Fiber(:A, [ListFormat(), ListFormat()], [:I, :J]), [AppendProtocol(), AppendProtocol()])
    B = Direct(Fiber(:B, [ArrayFormat(), ListFormat()], [:J, :K]), [LocateProtocol(), StepProtocol()])
    C = Direct(Fiber(:C, [ArrayFormat(), ListFormat()], [:I, :K]), [LocateProtocol(), StepProtocol()])

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

    A = Direct(Fiber(:A, [HashFormat(), HashFormat()], [:I, :J]), [InsertProtocol(), InsertProtocol()])
    B = Direct(Fiber(:B, [ListFormat(), ListFormat()], [:K, :J]), [StepProtocol(), StepProtocol()])
    C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:K, :I]), [StepProtocol(), StepProtocol()])

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

    #=

    B1 = Direct(B, [StepProtocol(), StepProtocol()], [2, 1])
C1 = Direct(C, [StepProtocol(), StepProtocol()], [1, 2])
w1r = Direct(Fiber(:w1, [], []), [], [])
w1w = Direct(Fiber(:w1, [], []), [], [])
prg = (@i @∀ j (
  (
    @∀ i (
      a[i] += *(w1r[], B1[j, i])
    )
  ) where (
    @∀ k (
      w1w[] += *(C1[j, k], d[k])
    )
  )
))
    Pigeon.Cup(Pigeon.Such(Pigeon.Times(Pigeon.Domain(j_14, :J), Pigeon.Domain(i_15, :I)), Pigeon.Exists(i_16, Pigeon.Wedge(Pigeon.Predicate(:B, i_15, j_14)))), Pigeon.Such(Pigeon.Times(Pigeon.Domain(j_2, :J), Pigeon.Domain(k_3, :K)), Pigeon.Exists(k_5, i_4, Pigeon.Wedge(Pigeon.Predicate(:B, i_4, j_2), Pigeon.Predicate(:C, j_2, k_3)))), Pigeon.Such(Pigeon.Times(Pigeon.Domain(j_22, :J)), Pigeon.Exists(k_23, Pigeon.Wedge(Pigeon.Predicate(:C, j_22, k_23)))))
    =#
end