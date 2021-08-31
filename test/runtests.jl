using Pigeon
using Test

@testset "Pigeon.jl" begin
    @test i":f(:B[i, k] * :C[k, j]^3, 42)" ==
    call(Literal(:f), call(Literal(*), access(Literal(:B), Name(:i), Name(:k)), call(Literal(^), access(Literal(:C), Name(:k), Name(:j)), Literal(3))), Literal(42))

    @test i"""
        ∀ i (
            ∀ j :A[i, j] += :w[j]
        with
            ∀ j, k :w[j] += :B[i, k] * :C[k, j]
        )
    """ ==
    loop(Name(:i), with(loop(Name(:j), assign(access(Literal(:A), Name(:i), Name(:j)), Literal(+), access(Literal(:w), Name(:j)))), loop(Name(:j), Name(:k), assign(access(Literal(:w), Name(:j)), Literal(+), call(Literal(*), access(Literal(:B), Name(:i), Name(:k)), access(Literal(:C), Name(:k), Name(:j)))))))

    A = Pigeon.HollowSymbolicTensor(:A, Literal(0))
    B = Pigeon.HollowSymbolicTensor(:B, Literal(0))
    println(Pigeon.make_style(Pigeon.AsymptoticAnalysis(), i"∀ i A[i] = B[i]"))
    println(Pigeon.AsymptoticAnalysis()(i"∀ i A[i] = B[i]"))
end
