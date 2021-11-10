using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:J, :I])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[j, i] * C[j, k] * d[k]

paper(prgm, [B, C, d],  [:I, :J, :K],"spmv2")
