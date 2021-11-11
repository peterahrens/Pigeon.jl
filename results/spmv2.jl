using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop i j k a[i] += B[i, j] * C[j, k] * d[k]

paper(prgm, [B, C, d], [:I, :J, :K], "spmv2")
