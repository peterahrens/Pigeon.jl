using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
c = Dense(:c, [:J])

prgm = @i @loop i j a[i] += B[i, j] * c[j]

paper(prgm, [B, c], [:I, :J], "spmv")
