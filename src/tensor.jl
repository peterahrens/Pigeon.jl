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
show_expression(io, mime, ::ArrayFormat) = print(io, "u")
struct ListFormat end
show_expression(io, mime, ::ListFormat) = print(io, "c")
struct HashFormat end
show_expression(io, mime, ::HashFormat) = print(io, "h")
struct NoFormat end
show_expression(io, mime, ::NoFormat) = print(io, "0")

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

function show_expression(io, mime, ex::SymbolicHollowDirector)
    print(io, getname(ex.tns))
    print(io, "{")
    format = getformat(ex)
    if length(format) >= 1
        for (lvl, proto) in zip(format, getprotocol(ex))
            show_expression(io, mime, proto)
            print(io, "(")
            show_expression(io, mime, lvl)
            print(io, ")")
        end
    end
    print(io, "}")
end

getname(tns::SymbolicHollowDirector) = getname(tns.tns)
rename(tns::SymbolicHollowDirector, name) = (tns = Base.copy(tns); tns.tns = rename(tns.tns, name); tns)

getformat(tns::SymbolicHollowDirector) = getformat(tns.tns)[tns.perm]
getprotocol(tns::SymbolicHollowDirector) = tns.protocol
getdefault(tns::SymbolicHollowDirector) = getdefault(tns.tns)
getsites(tns::SymbolicHollowDirector) = getsites(tns.tns)[tns.perm]

struct ConvertProtocol end
show_expression(io, mime, ::ConvertProtocol) = print(io, "_")
struct StepProtocol end
show_expression(io, mime, ::StepProtocol) = print(io, "s")
struct LocateProtocol end
show_expression(io, mime, ::LocateProtocol) = print(io, "l")
struct AppendProtocol end
show_expression(io, mime, ::AppendProtocol) = print(io, "a")
struct InsertProtocol end
show_expression(io, mime, ::InsertProtocol) = print(io, "i")

const coiter = StepProtocol()
const locate = LocateProtocol()

hasprotocol(fmt, ::ConvertProtocol) = true #Not sure

hasprotocol(::ArrayFormat, ::LocateProtocol) = true
hasprotocol(::ArrayFormat, ::AppendProtocol) = true #Not sure
hasprotocol(::ArrayFormat, ::InsertProtocol) = true

hasprotocol(::ListFormat, ::StepProtocol) = true
hasprotocol(::ListFormat, ::AppendProtocol) = true

hasprotocol(::HashFormat, ::LocateProtocol) = true
hasprotocol(::HashFormat, ::StepProtocol) = true
hasprotocol(::HashFormat, ::AppendProtocol) = true
hasprotocol(::HashFormat, ::InsertProtocol) = true

widenformat(fmt, proto) = hasprotocol(fmt, proto) ? fmt : error()

widenformat(fmt, ::ConvertProtocol) = fmt
widenformat(::NoFormat, ::LocateProtocol) = HashFormat()
widenformat(::NoFormat, ::StepProtocol) = ListFormat()
widenformat(::NoFormat, ::InsertProtocol) = HashFormat()
widenformat(::NoFormat, ::AppendProtocol) = ListFormat()
widenformat(::ListFormat, ::InsertProtocol) = HashFormat()
widenformat(::ArrayFormat, ::StepProtocol) = HashFormat()

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