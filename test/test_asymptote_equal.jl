@testset "asymptote_equality" begin
    using Pigeon: Such, Times, Wedge, Vee, Predicate, Cup, Cap, Empty
    a = Such(Times(:i, :j, :k), Wedge(Predicate(:A, :i, :j)))
    b = Cup(Such(Times(:i, :j, :k), Vee(Wedge(Predicate(:A, :i, :j), true), false)), Empty())
    @test Pigeon.asymptote_equal(a, b)
    @test Pigeon.asymptote_equal(a, b)
end