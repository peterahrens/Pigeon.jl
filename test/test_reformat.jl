using Pigeon
using Pigeon: ListFormat, ArrayFormat, HashFormat, NoFormat
using Pigeon: StepProtocol, LocateProtocol, AppendProtocol, InsertProtocol, ConvertProtocol

using Pigeon: Direct

using Pigeon: transform_reformat, concordize

function check_homomorphic(ref, test)
    if Pigeon.is_homomorphic(ref, test)
        return true
    end
    println("Reference:")
    display(ref)
    println()
    println("Test:")
    display(test)
    println()
    return false
end

@testset "transform_reformat" begin
    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [AppendProtocol(), AppendProtocol()])
    B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
    B_r1 = Direct(B, [LocateProtocol(), StepProtocol()])
    B_r2 = Direct(B, [LocateProtocol(), LocateProtocol()])

    prg = @i @loop i (
        @loop j (
            A[i, j] += B_r1[i, j] * B_r2[j, i]
        )
    )

    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [AppendProtocol(), AppendProtocol()])
    B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
    B_r1 = Direct(B, [LocateProtocol(), StepProtocol()])
    B_r2 = Direct(B, [ConvertProtocol(), ConvertProtocol()])
    B1 = Fiber(:B1, [ArrayFormat(), ArrayFormat()], [:I, :J])
    B1_r = Direct(B1, [LocateProtocol(), LocateProtocol()])
    B1_w = Direct(B1, [ConvertProtocol(), ConvertProtocol()])

    ref_prg = @i (@loop i j (
          A[i, j] += *(B_r1[i, j], B1_r[i, j])
        )) where (
          @loop i_3 j_2 (
            B1_w[i_3, j_2] = B_r2[j_2, i_3]
          )
        )

    @test check_homomorphic(ref_prg, transform_reformat(concordize(prg)))

    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [AppendProtocol(), AppendProtocol()])
    B = Fiber(:B, [ListFormat(), ListFormat(), ListFormat()], [:I, :K, :J])
    B_r = Direct(B, [StepProtocol(), StepProtocol(), StepProtocol()])

    prg = @i @loop i j k A[i, j] += B_r[i, k, j]

    B_r = Direct(B, [StepProtocol(), ConvertProtocol(), ConvertProtocol()])
    B1 = Fiber(:B1, [ListFormat(), ListFormat()], [:K, :J])
    B1_r = Direct(B1, [StepProtocol(), StepProtocol()])
    B1_w = Direct(B1, [ConvertProtocol(), ConvertProtocol()])

    ref_prg = @i (@loop i (
    (
        @loop j k (
            A[i, j] += B1_r[j, k]
        )
    ) where (
        @loop j_8 k_9 (
            B1_w[j_8, k_9] = B_r[i, k_9, j_8]
        )
    )))

    @test check_homomorphic(ref_prg, transform_reformat(concordize(prg))) 

    A = Direct(Fiber(:A, [ArrayFormat(), ListFormat()], [:J, :I]), [AppendProtocol(), InsertProtocol()])
    B = Direct(Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J]), [LocateProtocol(), StepProtocol()])

    prg = @i @loop i j A[j, i] += B[i, j]

    A = Direct(Fiber(:A, [ArrayFormat(), ListFormat()], [:J, :I]), [ConvertProtocol(), ConvertProtocol()])
    B = Direct(Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J]), [LocateProtocol(), StepProtocol()])
    A1 = Fiber(:A1, [HashFormat(), ListFormat()], [:J, :I])
    A1_r = Direct(A1, [ConvertProtocol(), ConvertProtocol()])
    A1_w = Direct(A1, [InsertProtocol(), AppendProtocol()])

    ref_prg = @i (@loop i_1 j_1 (
          A[j_1, i_1] = A1_r[i, j]
        )) where (
          @loop i j (
            A1_w[i,j] += B[i, j]
          )
        )

    @test check_homomorphic(ref_prg, transform_reformat(concordize(prg))) 

#=
    display(prg)

    display(Pigeon.transform_reformat(prg))

    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [LocateProtocol(), LocateProtocol()])
    B = Fiber(:B, [ListFormat(), ListFormat(), ListFormat()], [:I, :K, :J])
    B = Direct(B, [StepProtocol(), StepProtocol(), StepProtocol()])

    prg = @i @loop i (
        @loop j k (
            A[i, j] += B[i, k, j]
        )
    )

    display(prg)

    display(Pigeon.transform_reformat(prg))

    prg = @i @loop i (
        @loop j (
            A[i, j] += B1[i, j] * B2[i, j]
        )
    )

    display(prg)

    display(Pigeon.transform_reformat(prg))


    prg = @i @loop i (
        @loop j (
            A[i, j] += B1[i, j] * B3[i, j]
        )
    )

    display(prg)

    display(Pigeon.transform_reformat(prg))


    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [LocateProtocol(), LocateProtocol()])
    B = Fiber(:B, [ListFormat(), NoFormat()], [:I, :J])
    B_w = Direct(B, [AppendProtocol(), InsertProtocol()])
    B_r = Direct(B, [StepProtocol(), StepProtocol()])
    C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:I, :J]), [StepProtocol(), StepProtocol()])


    prg = @i (@loop i j (
        A[i, j] += B_r[i, j]
    )) where (@loop k l (
        B_w[k, l] += C[k, l]
    ))

    display(prg)

    display(Pigeon.normalize_index(Pigeon.transform_reformat(prg)))

    A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [LocateProtocol(), LocateProtocol()])
    B = Fiber(:B, [ListFormat(), NoFormat()], [:I, :J])
    B_w = Direct(B, [AppendProtocol(), InsertProtocol()])
    B_r = Direct(B, [StepProtocol(), StepProtocol()])
    C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:I, :J]), [StepProtocol(), StepProtocol()])


    prg = @i (@loop i j (
        A[i, j] += B_r[i, j]
    )) where (@loop k l (
        B_w[l, k] += C[k, l]
    ))

    display(prg)

    display(Pigeon.normalize_index(Pigeon.transform_reformat(prg)))
=#
#try \forall i j k l A[i,j] + A[k, l]
end
