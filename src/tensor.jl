abstract type AbstractSymbolicHollowTensor end
mutable struct SymbolicHollowTensor <: AbstractSymbolicHollowTensor
    name
    format
    dims
    default
    perm
    implicit
end
Base.copy(tns::SymbolicHollowTensor) = SymbolicHollowTensor(
    tns.name,
    tns.format,
    tns.dims,
    tns.default,
    tns.perm,
    tns.implicit)

#TODO this type probably needs a rework, but we will wait till we see what the enumerator needs
SymbolicHollowTensor(name, format, dims) = SymbolicHollowTensor(name, format, dims, 0)
SymbolicHollowTensor(name, format, dims, default) = SymbolicHollowTensor(name, format, dims, default, collect(1:length(dims)), false)

getname(tns::SymbolicHollowTensor) = tns.name
rename(tns::SymbolicHollowTensor, name) = (tns = Base.copy(tns); tns.name = name; tns)

getformat(tns::SymbolicHollowTensor) = tns.format

function show_expression(io, mime, ex::SymbolicHollowTensor)
    print(io, ex.name)
    print(io, "{")
    if length(ex.format) >= 1
        for lvl in ex.format
            show_expression(io, mime, lvl)
        end
    end
    print(io, "}")
end

mutable struct SymbolicSolidTensor
    name
    dims
    perm
end
Base.copy(tns::SymbolicSolidTensor) = SymbolicSolidTensor(
    tns.name,
    tns.dims,
    tns.perm)

#TODO this type probably needs a rework, but we will wait till we see what the enumerator needs
SymbolicSolidTensor(name, dims) = SymbolicSolidTensor(name, dims, collect(1:length(dims)))

getname(tns::SymbolicSolidTensor) = tns.name
rename(tns::SymbolicSolidTensor, name) = (tns = Base.copy(tns); tns.name = name; tns)

function show_expression(io, mime, ex::SymbolicSolidTensor)
    print(io, ex.name)
end