using Pigeon

include("paper.jl")

A = Fiber(:A, [ListFormat()], [:I])
B = Fiber(:B, [ListFormat()], [:I])
C = Fiber(:C, [ListFormat()], [:I])
D = Fiber(:D, [ListFormat()], [:I])

prgm = @i @loop i A[i] += B[i] + C[i] * D[i]

paper(prgm, [B, C, D], [], "bpctd")