@testset "Parse" begin
    @test i":f(:B[i, k] * :C[k, j]^3, 42)" ==
    call(Literal(:f), call(Literal(*), access(:B, Pigeon.Read(), Name(:i), Name(:k)), call(Literal(^), access(:C, Pigeon.Read(), Name(:k), Name(:j)), Literal(3))), Literal(42)) 

    @test i"""
        ∀ i (
            ∀ j :A[i, j] += :w[j]
        with
            ∀ j, k :w[j] += :B[i, k] * :C[k, j]
        )
    """ ==
    loop(Name(:i), with(loop(Name(:j), assign(access(:A, Pigeon.Update(), Name(:i), Name(:j)), Literal(+), access(:w, Pigeon.Read(), Name(:j)))), loop(Name(:j), Name(:k), assign(access(:w, Pigeon.Update(), Name(:j)), Literal(+), call(Literal(*), access(:B, Pigeon.Read(), Name(:i), Name(:k)), access(:C, Pigeon.Read(), Name(:k), Name(:j)))))))
end