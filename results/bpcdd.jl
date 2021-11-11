using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:I, :J])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:I, :J])

prgm = @i @loop i j A[i, j] += (B[i, j] + C[i, j]) * D[i, j]

paper(prgm, [B, C, D], [:I, :J], "bpcdd")