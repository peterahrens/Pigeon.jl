using Pigeon

include("paper.jl")

A = Fiber(:A, [ArrayFormat(), ListFormat()], [:I, :I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])

prgm = @i @loop i j k A[i, j] += B[i, k] * B[j, k]

paper(prgm, [B,], "ata")
