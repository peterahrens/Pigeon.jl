using Pigeon
using Pigeon: ListFormat, ArrayFormat, HashFormat
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

prg = @i @loop i (
	@loop j (
		A[i, j] += B1[i, j] * B3[i, j]
    )
)

display(prg)

display(Pigeon.transform_reformat(prg))

#try \forall i j k l A[i,j] + A[k, l]