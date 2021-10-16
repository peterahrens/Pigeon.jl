abstract type SymbolicLevel end

struct SymbolicUncompressedLevel <: SymbolicLevel end
struct SymbolicCompressedLevel <: SymbolicLevel end
struct SymbolicHashedLevel <: SymbolicLevel end

struct SymbolicSparseTensor
    levels
    dims
    default
end

struct Locate end
struct Coiterate end

struct ReformattedSymbolicSparseTensor
    tns
    perm
    props
end