using Pigeon
using Test

@testset "Pigeon.jl" begin
    A = Pigeon.HollowSymbolicTensor(:A, Literal(0))
    B = Pigeon.HollowSymbolicTensor(:B, Literal(0))
    println(Pigeon.make_style(Pigeon.AsymptoticAnalysis(), i"∀ i $A[i] = $B[i]"))
    println(Pigeon.AsymptoticAnalysis()(i"∀ i $A[i] = $B[i]"))
end
