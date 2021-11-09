using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:K, :L])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:L, :J])

prgm = @i @loop i j k l A[i, j] += B[i, k] * C[k, l] * D[l, j]

paper(prgm, [B,C,D], "spgemm2")
