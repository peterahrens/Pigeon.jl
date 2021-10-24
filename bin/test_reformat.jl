using Pigeon
using Pigeon: ListFormat, ArrayFormat, HashFormat, NoFormat
using Pigeon: StepProtocol, LocateProtocol, AppendProtocol, InsertProtocol

using Pigeon: Direct

A = Direct(Fiber(:A, [ArrayFormat(), ArrayFormat()], [:I, :J]), [LocateProtocol(), LocateProtocol()])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
B1 = Direct(B, [LocateProtocol(), StepProtocol()])
B2 = Direct(B, [LocateProtocol(), LocateProtocol()])
B3 = Direct(B, [StepProtocol(), LocateProtocol()])

prg = @i @loop i (
	@loop j (
		A[i, j] += B1[i, j] * B2[i, j]
    )
)

display(prg)

display(Pigeon.transform_reformat(prg))

prg = Pigeon.concordize(@i @loop i (
	@loop j (
		A[i, j] += B1[i, j] * B2[j, i]
    )
))

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

#try \forall i j k l A[i,j] + A[k, l]