using Pigeon
using Test

@testset "Pigeon.jl" begin
    i"f(B[i, k] * C[k, j]^3, 42)"

    i"""
        ∀ i (
            ∀ j A[i, j] += w[j]
        with
            ∀ j, k w[j] += B[i, k] * C[k, j]
        )
    """

    A = Pigeon.HollowSymbolicTensor(:A, Literal(0))
    B = Pigeon.HollowSymbolicTensor(:B, Literal(0))
    println(Pigeon.make_style(Pigeon.AsymptoticAnalysis(), i"∀ i $A[i] = $B[i]"))
    println(Pigeon.AsymptoticAnalysis()(i"∀ i $A[i] = $B[i]"))
end
