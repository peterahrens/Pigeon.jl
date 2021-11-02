using Pigeon

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[i, j] * C[j, k] * d[k]

println(Pigeon.lower_taco(prgm))