using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat(), ListFormat()], [:I, :K, :L])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:K, :J])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:L, :J])

prgm = @i @loop i j k l A[i, j] += B[i, k, l] * C[k, j] * D[l, j]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "smttkrp")
