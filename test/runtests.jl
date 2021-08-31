using Pigeon
using Test

@testset "Pigeon.jl" begin
    @test i"f(:B[i, k] * :C[k, j]^3, 42)" ==
        call(:f, call(*, access(:B, Name(:i), Name(:k)), call(^, access(:C, Name(:k), Name(:j)), 3)), 42)

    @test i"""
        ∀ i (
            ∀ j :A[i, j] += :w[j]
        with
            ∀ j, k w[j] += :B[i, k] * :C[k, j]
        )
    """ == loop(Name(:i),
            with(loop(Name(:j),
                assign(access(:A, Name(:i), Name(:j)), Literal(+), access(:w, Name(:j)))),
                loop(Name(:j), Name(:k), assign(access(:w, Name(:j)), Literal(+),
                    call(*, access(:B, Name(:i), Name(:k)), access(:C, Name(:k), Name(:j)))))))


    A = Pigeon.HollowSymbolicTensor(:A, Literal(0))
    B = Pigeon.HollowSymbolicTensor(:B, Literal(0))
    println(Pigeon.make_style(Pigeon.AsymptoticAnalysis(), i"∀ i A[i] = B[i]"))
    println(Pigeon.AsymptoticAnalysis()(i"∀ i A[i] = B[i]"))
end
