using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:K, :J])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:K, :J])

prgm = @i @loop i j k A[i, j] += B[i, k] * C[k, j] * D[k, j]

paper(prgm, [B,C,D], [:I, :J, :K], "spgemmh")
