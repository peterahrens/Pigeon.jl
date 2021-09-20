@testset "containment" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists, Domain
    using Pigeon: isdominated
    @test isdominated(Empty(), Empty())
    @test isdominated(Empty(), Times())
    @test !isdominated(Times(), Empty())

    @test isdominated(Empty(), Such(Times(), true))
    @test !isdominated(Such(Times(), true), Empty())

    @test isdominated(Empty(), Such(Times(Domain(:i, :I)), false))
    @test isdominated(Such(Times(Domain(:i, :I)), false), Empty())


    @test isdominated(Such(Times(Domain(:i, :I)), false), Such(Times(Domain(:i, :I)), true))
    @test !isdominated(Such(Times(Domain(:i, :I)), true), Such(Times(Domain(:i, :I)), false))

    @test isdominated(Such(Times(), Predicate(:A)), Such(Times(), Predicate(:A)))
    @test isdominated(Such(Times(), Wedge(Predicate(:A), Predicate(:B))), Such(Times(), Predicate(:A)))

    @test isdominated(Such(Times(Domain(:i, :I)), Predicate(:A, :i)), Such(Times(Domain(:j, :I)), Predicate(:A, :j)))
    @test isdominated(Such(Times(Domain(:i, :I)), Wedge(Predicate(:A, :i), Predicate(:B, :i))), Such(Times(Domain(:i, :I)), Predicate(:B, :i)))
    @test !isdominated(Such(Times(Domain(:i, :I)), Predicate(:A, :i)), Such(Times(Domain(:i, :I)), Predicate(:B, :i)))

    @test isdominated(
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j)),
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Exists(:j, Predicate(:A, :i, :j)))
    )

    @test !isdominated(
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Exists(:j, Predicate(:A, :i, :j))),
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j))
    )

    @test !isdominated(
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j)),
        Such(Times(Domain(:i, :I)), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(Domain(:i, :I)), Predicate(:A, :i, :j)),
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(Domain(:i, :I)), Exists(:j, Predicate(:A, :i, :j))),
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(Domain(:i, :I), Domain(:j, :J)), Predicate(:A, :i, :j)),
        Such(Times(Domain(:j, :J), Domain(:i, :I)), Predicate(:A, :i, :j))
    )

    @test isdominated(
        Such(Times(Domain(:k, :I), Domain(:l, :J)), Predicate(:A, :k, :l)),
        Such(Times(Domain(:j, :J), Domain(:i, :I)), Predicate(:A, :i, :j))
    )

    @test !isdominated(
        Such(Times(Domain(:k, :K), Domain(:l, :L)), Predicate(:A, :k, :k)),
        Such(Times(Domain(:j, :J), Domain(:i, :I)), Predicate(:A, :i, :j))
    )

    @test isdominated(
        Such(Times(), Exists(:i, Wedge(Predicate(:A, :i), Predicate(:B, :i)))),
        Such(Times(), Exists(:i, :j, Wedge(Predicate(:A, :i), Predicate(:B, :j)))),
    )

    @test isdominated(
        Such(Times(Domain(:i, :I)), Wedge(Predicate(:A, :i), Predicate(:B, :i))),
        Such(Times(Domain(:i, :I)), Exists(:j, Wedge(Predicate(:A, :i), Predicate(:B, :j)))),
    )

    @test !isdominated(
        Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K), Domain(:l, :L)), Wedge(Predicate(:A, :i, :j, :k, :l), Predicate(:B, :i, :j, :k, :l))),
        Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K), Domain(:l, :L)), Wedge(Predicate(:A, :i, :i, :i, :i), Predicate(:B, :i, :i, :i, :i))),
    )

    a = Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K)), Wedge(Predicate(:A, :i, :j)))
    b = Cup(Such(Times(Domain(:i, :I), Domain(:j, :J), Domain(:k, :K)), Vee(Wedge(Predicate(:A, :i, :j), true), false)), Empty())
    @test isdominated(a, b)
end