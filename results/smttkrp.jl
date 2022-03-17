using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat(), ListFormat()], [:I, :K, :L])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:J, :L])

prgm = @i @loop i j k l A[i, j] += B[i, k, l] * C[j, k] * D[j, l]

paper(prgm, [B, C, D], [:I, :J, :K, :L], "smttkrp")
