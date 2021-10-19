abstract type AbstractSymbolicHollowTensor end
mutable struct SymbolicHollowTensor <: AbstractSymbolicHollowTensor
    name
    format
    dims
    default
    perm
end
Base.copy(tns::SymbolicHollowTensor) = SymbolicHollowTensor(
    tns.name,
    tns.format,
    tns.dims,
    tns.default,
    tns.perm)

#TODO this type probably needs a rework, but we will wait till we see what the enumerator needs
SymbolicHollowTensor(name, format, dims) = SymbolicHollowTensor(name, format, dims, 0)
SymbolicHollowTensor(name, format, dims, default) = SymbolicHollowTensor(name, format, dims, default, collect(1:length(dims)))

getname(tns::SymbolicHollowTensor) = tns.name
rename(tns::SymbolicHollowTensor, name) = (tns = Base.copy(tns); tns.name = name; tns)

getformat(tns::SymbolicHollowTensor) = tns.format
getdefault(tns::SymbolicHollowTensor) = tns.default
getsites(tns::SymbolicHollowTensor) = tns.perm

hasprotocol(fmt, proto) = false

struct ArrayFormat end
struct ListFormat end
struct HashFormat end

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

mutable struct SymbolicHollowDirector <: AbstractSymbolicHollowTensor
    tns
    protocol
    perm
end
Base.copy(tns::SymbolicHollowDirector) = SymbolicHollowDirector(
    tns.tns,
    tns.protocol,
    tns.perm)


SymbolicHollowDirector(tns, protos) = SymbolicHollowDirector(tns, protos, collect(1:length(protos)))


getname(tns::SymbolicHollowDirector) = getname(tns.tns)
rename(tns::SymbolicHollowDirector, name) = (tns = Base.copy(tns); tns.tns = rename(tns.tns, name); tns)

getformat(tns::SymbolicHollowDirector) = getformat(tns.tns)[tns.perm]
getprotocol(tns::SymbolicHollowDirector) = tns.protocol
getdefault(tns::SymbolicHollowDirector) = getdefault(tns.tns)
getsites(tns::SymbolicHollowDirector) = getsites(tns.tns)[tns.perm]

struct StepProtocol end
struct LocateProtocol end
struct AppendProtocol end
struct InsertProtocol end

const coiter = StepProtocol()
const locate = LocateProtocol()

hasprotocol(::ArrayFormat, ::LocateProtocol) = true
hasprotocol(::ArrayFormat, ::AppendProtocol) = true #Not sure
hasprotocol(::ArrayFormat, ::InsertProtocol) = true

hasprotocol(::ListFormat, ::StepProtocol) = true
hasprotocol(::ListFormat, ::AppendProtocol) = true

hasprotocol(::HashFormat, ::LocateProtocol) = true
hasprotocol(::HashFormat, ::StepProtocol) = true
hasprotocol(::HashFormat, ::AppendProtocol) = true
hasprotocol(::HashFormat, ::InsertProtocol) = true

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
getsites(tns::SymbolicSolidTensor) = tns.perm

function show_expression(io, mime, ex::SymbolicSolidTensor)
    print(io, ex.name)
end