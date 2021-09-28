@testset "SSA" begin
    @name A B C D w_1 w_2 w_3
    @test Pigeon.@ex Pigeon.@capture Pigeon.transform_ssa(@i(
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
    )) @i(
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
end