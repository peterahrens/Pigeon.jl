using Pigeon
using Test

@testset "Pigeon.jl" begin
    @test i":f(:B[i, k] * :C[k, j]^3, 42)" ==
    call(Literal(:f), call(Literal(*), access(:B, Name(:i), Name(:k)), call(Literal(^), access(:C, Name(:k), Name(:j)), Literal(3))), Literal(42)) 

    @test i"""
        ∀ i (
            ∀ j :A[i, j] += :w[j]
        with
            ∀ j, k :w[j] += :B[i, k] * :C[k, j]
        )
    """ ==
    loop(Name(:i), with(loop(Name(:j), assign(access(:A, Name(:i), Name(:j)), Literal(+), access(:w, Name(:j)))), loop(Name(:j), Name(:k), assign(access(:w, Name(:j)), Literal(+), call(Literal(*), access(:B, Name(:i), Name(:k)), access(:C, Name(:k), Name(:j)))))))

    Pigeon.@name A B C D w_1 w_2

    @test Set(normalize_index.(saturate_index(i"A[i, j] += B[] + C[] + D[]"))) == Set(normalize_index.([
        i"""
        A[i, j] += +(B[], D[], C[])
        """,

        i"""
        (
        A[i, j] += +(w_1[], C[])

        with
        w_1[] = +(B[], D[])
        )
        """,

        i"""
        (
        A[i, j] += +(D[], w_1[])

        with
        w_1[] = +(B[], C[])
        )
        """,

        i"""
        (
        A[i, j] += +(B[], w_1[])

        with
        w_1[] = +(D[], C[])
        )
        """
    ]))

    A = Pigeon.HollowSymbolicTensor(:A, Literal(0))
    B = Pigeon.HollowSymbolicTensor(:B, Literal(0))

    #@test Pigeon.AsymptoticAnalysis()(i"∀ i A[i] = B[i]") == Pigeon.Cup(Pigeon.Cup(false, Pigeon.Cup(Pigeon.Cup(false, false), Pigeon.Cup(false, false))), Pigeon.Cup(Pigeon.Cup(Pigeon.Cup(Pigeon.Such(Pigeon.Times(Name(:i)), Pigeon.Wedge(Pigeon.Exists(Pigeon.Predicate(:A, :i)), Pigeon.Exists(Pigeon.Predicate(:B, :i)))), Pigeon.Such(Pigeon.Times(Name(:i)), Pigeon.Wedge(true, Pigeon.Exists(Pigeon.Predicate(:B, :i))))), Pigeon.Such(Pigeon.Times(Name(:i)), Pigeon.Wedge(Pigeon.Exists(Pigeon.Predicate(:A, :i)), true))), Pigeon.Such(Pigeon.Times(Name(:i)), Pigeon.Wedge(true, true))))
    #Pigeon.@name A B C D w_1


end