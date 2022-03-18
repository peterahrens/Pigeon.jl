using Pigeon

a = Dense(:a, [:I])
B = Fiber(:B, [ArrayFormat(), ListFormat()], [:I, :J])
C = Fiber(:C, [ArrayFormat(), ListFormat()], [:J, :K])
d = Dense(:d, [:K])

prgm = @i @loop k j i a[i] += B[i, j] * C[j, k] * d[k]

frontier = Pigeon.autoschedule(prgm, sunk_costs = [Pigeon.Domain(:j, :J); map(Pigeon.read_cost, [a, B, C, d])], assumptions=map(Pigeon.assume_nonempty, [B, C]), protocolize=Pigeon.tacoprotocolize)

foreach(display, frontier)

println("foo")

frontier = Pigeon.saturate_index(prgm)
frontier = Pigeon.filter_pareto(frontier, by = kernel -> Pigeon.maxdepth(kernel))

foreach(display, frontier)
