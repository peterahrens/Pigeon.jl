@testset "SSA" begin
    @name A B C D w_1 w_2 w_3
    ex = Pigeon.transform_ssa(@i(
        @loop i (
            @loop j (
                @loop j (
                        A[i, j] += A[i] * C[i, j]
                    ) where (
                        (
                            A[i] += C[j]
                        ) where (
                            C[j] += D[j]
                        )
                    )
            )
        )
    ))

    @test Pigeon. Pigeon.@capture ex @i(
        @loop i (
            @loop j (
                @loop ~j_1 (
                        (~A_1)[i, ~j_1] += (~A_1)[i] * (~C_1)[i, ~j_1]
                    ) where (
                        (
                            A[i] += C[~j_1]
                        ) where (
                            C[~j_1] += D[~j_1]
                        )
                    )
            )
        )
    )

    @test ex == Pigeon.transform_ssa(ex) #fixpoint

    using Pigeon: Such, Times, Domain, Wedge, Exists, Predicate

    ex = Pigeon.transform_ssa(
        Times(Domain(:k, :J), Domain(:l, :J), Such(Times(Domain(:i, :I), Domain(:j, :J)), Wedge(Exists(:i, Predicate(:A, :i, :j)), Predicate(:A, :i, :j))))
    )

    @test Pigeon. Pigeon.@capture ex (
        Times(Domain(:k, :J), Domain(:l, :J), Such(Times(Domain(:i, :I), Domain(:j, :J)), Wedge(Exists(~i_1, Predicate(:A, ~i_1, :j)), Predicate(:A, :i, :j))))
    )

    @test ex == Pigeon.transform_ssa(ex) #fixpoint
end