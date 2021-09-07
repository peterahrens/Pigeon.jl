@testset "SSA" begin
    @name A B C D w_1 w_2 w_3
    @test Pigeon.@ex Pigeon.@capture Pigeon.transform_ssa(i"""
        ∀ i
            ∀ j
                ∀ j (
                        A[i, j] += A[i] * C[i, j]
                    with
                        A[i] += D[j]
                    )
    """) i"""
        ∀ i
            ∀ j
                ∀ (~j_1) (
                        A[i, ~j_1] += (~A_1)[i] * C[i, ~j_1]
                    with
                        (~A_1)[i] += D[~j_1]
                    )
    """p 

    display(Pigeon.transform_ssa(i"""
    ∀ i
        ∀ j
            ∀ j (
                    A[i, j] += A[i] * C[i, j]
                with
                    A[i] += D[j]
                )
    """))
end