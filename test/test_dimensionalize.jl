@testset "dimensionalize" begin
    struct TestDimensionalizeTensor
        name
        dims
    end
    struct TestDimensionalizeContext end
    Pigeon.getname(tns::TestDimensionalizeTensor) = tns.name
    Pigeon.lower_axes(tns::TestDimensionalizeTensor, ::TestDimensionalizeContext) = tns.dims
    Pigeon.lower_axis_merge(::TestDimensionalizeContext, a, b) = (@assert a == b; a)
    Pigeon.rename(tns::TestDimensionalizeTensor, name) = TestDimensionalizeTensor(name, tns.dims)
    A = TestDimensionalizeTensor(:A, [1, 10, 12])
    B = TestDimensionalizeTensor(:B, [3, 1, 10])
    dims = Pigeon.dimensionalize(Pigeon.transform_ssa(i"""
        ∀ i, j, k, l A[i, j, k] += B[l, i, j]
    """), TestDimensionalizeContext())
    @test dims[:i] == 1
    @test dims[:j] == 10
    @test dims[:k] == 12
    @test dims[:l] == 3

    A = TestDimensionalizeTensor(:A, [1,])
    B = TestDimensionalizeTensor(:B, [3])
    @test_throws AssertionError Pigeon.dimensionalize(Pigeon.transform_ssa(i"""
        ∀ i A[i,] += B[i,]
    """), TestDimensionalizeContext())
end