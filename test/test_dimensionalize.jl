@testset "dimensionalize" begin
    struct TestDimensionalizeTensor
        name
        dims
    end
    struct TestDimensionalizeContext
        dims
    end
    Pigeon.visit!(root, ::TestDimensionalizeContext, ::Pigeon.DefaultStyle) = nothing
    Pigeon.getdims(ctx::TestDimensionalizeContext) = ctx.dims
    Pigeon.getname(tns::TestDimensionalizeTensor) = tns.name
    Pigeon.getsites(tns::TestDimensionalizeTensor) = 1:length(tns.dims)
    Pigeon.lower_axes(tns::TestDimensionalizeTensor, ::TestDimensionalizeContext) = tns.dims
    Pigeon.lower_axis_merge(::TestDimensionalizeContext, a, b) = (@assert a == b; a)
    Pigeon.rename(tns::TestDimensionalizeTensor, name) = TestDimensionalizeTensor(name, tns.dims)
    A = TestDimensionalizeTensor(:A, [1, 10, 12])
    B = TestDimensionalizeTensor(:B, [3, 1, 10])
    ctx = TestDimensionalizeContext(Pigeon.Dimensions())
    Pigeon.visit!(Pigeon.transform_ssa(@i(
        @loop i j k l A[i, j, k] += B[l, i, j]
    )), ctx, Pigeon.DimensionalizeStyle())
    @test ctx.dims[:i] == 1
    @test ctx.dims[:j] == 10
    @test ctx.dims[:k] == 12
    @test ctx.dims[:l] == 3

    A = TestDimensionalizeTensor(:A, [1,])
    B = TestDimensionalizeTensor(:B, [3])
    ctx = TestDimensionalizeContext(Pigeon.Dimensions())
    @test_throws AssertionError Pigeon.visit!(Pigeon.transform_ssa(@i(
        @loop i A[i,] += B[i,]
    )), ctx, Pigeon.DimensionalizeStyle())

    A = TestDimensionalizeTensor(:A, [2])
    B = TestDimensionalizeTensor(:B, [2])
    C = TestDimensionalizeTensor(:C, [2])
    w = TestDimensionalizeTensor(:w, [2])
    w′ = TestDimensionalizeTensor(:w, [2])
    ctx = TestDimensionalizeContext(Pigeon.Dimensions())
    Pigeon.visit!(@i(
        (@loop i A[i] += B[i] * w[i]) where (@loop j w′[j] += C[j])
    ), ctx, Pigeon.DimensionalizeStyle())
    @test ctx.dims[:i] == 2
    @test ctx.dims[:j] == 2
end