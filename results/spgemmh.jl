using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:J, :K])

prgm = @i @loop i j k A[i, j] += B[i, k] * C[j, k] * D[j, k]

paper(prgm, [B,C,D], [:I, :J, :K], "spgemmh")
