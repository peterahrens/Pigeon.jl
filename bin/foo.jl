using Pigeon

a = Dense(:a, [:I])
B = Direct(Fiber(:B, [ArrayFormat(), ListFormat()], [:J, :I]), [LocateProtocol(), StepProtocol()], [1, 2])
C = Direct(Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K]), [LocateProtocol(), StepProtocol()])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[j, i] * C[j, k] * d[k]

println(Pigeon.lower_taco(Pigeon.transform_reformat(Pigeon.concordize(prgm))))
println(Pigeon.build_taco(Pigeon.transform_reformat(Pigeon.concordize(prgm))))