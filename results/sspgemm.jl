using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:I, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:J, :K])

prgm = @i @loop i j k A[i, j] += B[i, j] * C[i, k] * D[j, k]

paper(prgm, [B,C,D], [:I, :J, :K], "sspgemm")
