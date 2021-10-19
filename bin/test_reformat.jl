using Pigeon

A = Fiber(:A, [locate, locate], [:I, :J])
B1 = Fiber(:B, [locate, coiter], [:I, :J])
B2 = Fiber(:B, [locate, locate], [:I, :J])

prg = @i @∀ i (
	@∀ j (
		A[i, j] += B1[i, j] * B2[i, j]
    )
)

println(Pigeon.transform_reformat(prg))