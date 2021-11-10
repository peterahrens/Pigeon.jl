using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:I, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:K, :J])

prgm = @i @loop i j k A[i, j] += B[i, j] * C[i, k] * D[k, j]

paper(prgm, [B,C,D], [:I, :J, :K], "sspgemm")