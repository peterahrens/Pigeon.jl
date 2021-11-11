using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:K, :L])
e = Dense(:e, [:L])

prgm = @i @loop i j k l a[i] += B[i, j] * C[j, k] * D[k, l] * e[l]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "spmv3")