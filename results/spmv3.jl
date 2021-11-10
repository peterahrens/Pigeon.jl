using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:J, :I])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:K, :L])
e = Dense(:e, [:L])

prgm = @i @loop k j i a[i] += B[j, i] * C[j, k] * D[k, l] * e[l]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "spmv3")
