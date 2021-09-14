@testset "containment" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty, Exists
    using Pigeon: isdominated
    @test isdominated(Empty(), Empty())
    @test isdominated(Empty(), Times())
    @test !isdominated(Times(), Empty())

    @test isdominated(Empty(), Such(Times(), true))
    @test !isdominated(Such(Times(), true), Empty())

    @test isdominated(Empty(), Such(Times(:i), false))
    @test isdominated(Such(Times(:i), false), Empty())


    @test isdominated(Such(Times(:i), false), Such(Times(:i), true))
    @test !isdominated(Such(Times(:i), true), Such(Times(:i), false))

    @test isdominated(Such(Times(), Predicate(:A)), Such(Times(), Predicate(:A)))
    @test isdominated(Such(Times(), Wedge(Predicate(:A), Predicate(:B))), Such(Times(), Predicate(:A)))

    @test isdominated(Such(Times(:i), Predicate(:A, :i)), Such(Times(:i), Predicate(:A, :i)))
    @test isdominated(Such(Times(:i), Wedge(Predicate(:A, :i), Predicate(:B, :i))), Such(Times(:i), Predicate(:B, :i)))
    @test !isdominated(Such(Times(:i), Predicate(:A, :i)), Such(Times(:i), Predicate(:B, :i)))

    @test isdominated(
        Such(Times(:i, :j), Predicate(:A, :i, :j)),
        Such(Times(:i, :j), Exists(:j, Predicate(:A, :i, :j)))
    )
    @test !isdominated(
        Such(Times(:i, :j), Exists(:j, Predicate(:A, :i, :j))),
        Such(Times(:i, :j), Predicate(:A, :i, :j))
    )

    @test !isdominated(
        Such(Times(:i, :j), Predicate(:A, :i, :j)),
        Such(Times(:i), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(:i), Predicate(:A, :i, :j)),
        Such(Times(:i, :j), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(:i), Exists(:j, Predicate(:A, :i, :j))),
        Such(Times(:i, :j), Predicate(:A, :i, :j))
    )
    @test isdominated(
        Such(Times(:i, :j), Predicate(:A, :i, :j)),
        Such(Times(:j, :i), Predicate(:A, :i, :j))
    )

    @test isdominated(
        Such(Times(:k, :l), Predicate(:A, :k, :l)),
        Such(Times(:j, :i), Predicate(:A, :i, :j))
    )

    @test !isdominated(
        Such(Times(:k, :l), Predicate(:A, :k, :k)),
        Such(Times(:j, :i), Predicate(:A, :i, :j))
    )

    @test isdominated(
        Such(Times(), Exists(:i, Wedge(Predicate(:A, :i), Predicate(:B, :i)))),
        Such(Times(), Exists(:i, :j, Wedge(Predicate(:A, :i), Predicate(:B, :j)))),
    )

    @test isdominated(
        Such(Times(:i), Wedge(Predicate(:A, :i), Predicate(:B, :i))),
        Such(Times(:i), Exists(:j, Wedge(Predicate(:A, :i), Predicate(:B, :j)))),
    )

    @test !isdominated(
        Such(Times(:i, :j, :k, :l), Wedge(Predicate(:A, :i, :j, :k, :l), Predicate(:B, :i, :j, :k, :l))),
        Such(Times(:i, :j, :k, :l), Wedge(Predicate(:A, :i, :i, :i, :i), Predicate(:B, :i, :i, :i, :i))),
    )

    a = Such(Times(:i, :j, :k), Wedge(Predicate(:A, :i, :j)))
    b = Cup(Such(Times(:i, :j, :k), Vee(Wedge(Predicate(:A, :i, :j), true), false)), Empty())
    @test isdominated(a, b)
end