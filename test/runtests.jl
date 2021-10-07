using Pigeon
using Test

@testset "Pigeon.jl" begin
    include("test_parse.jl")
    include("test_ssa.jl")
    include("test_dimensionalize.jl")
    include("test_containment.jl")
    include("test_lower_asymptote.jl")
end