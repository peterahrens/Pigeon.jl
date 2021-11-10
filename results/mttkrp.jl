using Pigeon

include("paper.jl")

A = Dense(:A, [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat(), ListFormat()], [:I, :K, :L])
C = Dense(:C, [:K, :J])
D = Dense(:D, [:L, :J])

prgm = @i @loop i j k A[i, j] += B[i, k, l] * C[k, j] * D[l, j]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "mttkrp")