using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])

prgm = @i @loop i j k A[i, j] += B[i, k] * C[j, k]

paper(prgm, [B, C], [:I, :J, :K], "spgemm")
