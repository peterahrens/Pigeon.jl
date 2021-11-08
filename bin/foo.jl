using Pigeon

include("paper.jl")

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:J, :I])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[j, i] * C[j, k] * d[k]

#println(Pigeon.lower_taco(Pigeon.transform_reformat(Pigeon.concordize(prgm))))
#println(Pigeon.build_taco(Pigeon.transform_reformat(Pigeon.concordize(prgm))))
#println(Pigeon.run_taco(Pigeon.transform_reformat(Pigeon.concordize(prgm)), Pigeon.generate_uniform_taco_inputs([a, B, C, d], 100, 0.1)))

paper(prgm, [B, C, d], "spmmv")
