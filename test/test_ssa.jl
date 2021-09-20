@testset "SSA" begin
    @name A B C D w_1 w_2 w_3
    @test Pigeon.@ex Pigeon.@capture Pigeon.transform_ssa(@i(
        @loop i (
            @loop j (
                @loop j (
                        A[i, j] += A[i] * C[i, j]
                    ) where (
                        A[i] += D[j]
                    )
            )
        )
    )) @i(
        @loop i (
            @loop j (
                @loop ~j_1 (
                        A[i, ~j_1] += (~A_1)[i] * C[i, ~j_1]
                    ) where (
                        (~A_1)[i] += D[~j_1]
                    )
            )
        )
    )
end