using Pigeon
using Pigeon: InsertProtocol

A = Direct(Fiber(:A, [HashFormat(), HashFormat()], [:I, :J]), [InsertProtocol(), InsertProtocol()])
B = Direct(Fiber(:B, [ListFormat(), ListFormat()], [:I, :K]), [StepProtocol(), StepProtocol()])
C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:J, :K]), [StepProtocol(), StepProtocol()])

ex = @i @loop i j k A[i,j] += B[i, k] * C[j, k]
display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(ex)))

A = Direct(Fiber(:A, [HashFormat(), HashFormat()], [:I, :J]), [InsertProtocol(), InsertProtocol()])
B = Direct(Fiber(:B, [ListFormat(), ListFormat()], [:I, :K]), [StepProtocol(), StepProtocol()])
C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:K, :J]), [StepProtocol(), StepProtocol()])

ex = @i @loop i k j A[i,j] += B[i, k] * C[k, j]
display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(ex)))

A = Direct(Fiber(:A, [HashFormat(), HashFormat()], [:I, :J]), [InsertProtocol(), InsertProtocol()])
B = Direct(Fiber(:B, [ListFormat(), ListFormat()], [:K, :I]), [StepProtocol(), StepProtocol()])
C = Direct(Fiber(:C, [ListFormat(), ListFormat()], [:K, :J]), [StepProtocol(), StepProtocol()])

ex = @i @loop k i j A[i,j] += B[k, i] * C[k, j]
display(Pigeon.supersimplify_asymptote(Pigeon.asymptote(ex)))
