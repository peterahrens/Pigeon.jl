using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :J])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :K])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:K, :L])
D = Fiber(:D, [ArrayFormat(), ListFormat()], [:J, :L])

prgm = @i @loop i j k l A[i, j] += B[i, k] * C[k, l] * D[j, l]

paper(prgm, [B,C,D],[:I, :J, :K, :L], "spgemm2")
