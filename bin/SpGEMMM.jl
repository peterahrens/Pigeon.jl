using Pigeon
using Pigeon: Predicate, Wedge, Exists

A = Fiber(:A, [HashFormat(), HashFormat()], [:I, :J])
B = Fiber(:B, [HashFormat(), HashFormat()], [:I, :K])
C = Fiber(:C, [HashFormat(), HashFormat()], [:I, :K])
D = Fiber(:D, [HashFormat(), HashFormat()], [:K, :J])

prgm = @i @loop k j i A[i, j] += B[i, k] * C[i, k] * D[k, j]

frontier = Pigeon.autoschedule(prgm, sunk_costs = map(Pigeon.read_cost, [B, C, D]), assumptions=[map(Pigeon.assume_nonempty, [A, B, C]); Exists(:ii, :kk, Wedge(Predicate(:B, :ii, :kk), Predicate(:C, :ii, :kk)))])

foreach(display, frontier)