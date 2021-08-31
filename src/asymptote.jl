abstract type AsymptoteNode end
abstract type AsymptotePredicate <: AsymptoteNode end
abstract type AsymptoteSet <: AsymptoteNode end

function Base.show(io::IO, mime::MIME"text/plain", ex::AsymptoteNode)
	print(io, "\"")
	show_asymptote(io, mime, ex)
	print(io, "\"\n")
end

function Base.:(==)(a::T, b::T) where {T <: AsymptoteNode}
    if istree(a) && istree(b)
        (operation(a) == operation(b)) && 
        (arguments(a) == arguments(b))
    else
        invoke(==, Tuple{Any, Any}, a, b)
    end
end

function Base.show(io::IO, ex::AsymptoteNode)
    if istree(ex)
        print(io, operation(ex))
        print(io, "(")
        for arg in arguments(ex)[1:end-1]
            show(io, arg)
            print(io, ", ")
        end
        if length(arguments(ex)) >= 1
            show(io, last(arguments(ex)))
        end
        print(io, ")")
    else
        invoke(show, Tuple{IO, Any}, io, ex)
    end
end

show_asymptote_undelimited(io, mime, ex) = 
    show_asymptote(io, mime, ex)

bases(ex) = [ex]

struct Forall <: AsymptoteNode
    idxs::Vector{Any}
    arg::Any
    Forall(args...) = new(collect(args[1:end-1]), args[end])
end

SymbolicUtils.istree(ex::Forall) = true
SymbolicUtils.operation(ex::Forall) = Forall
SymbolicUtils.arguments(ex::Forall) = [ex.idxs;[ex.arg]]

struct Exists <: AsymptoteNode
    idxs::Vector{Any}
    arg::Any
    Exists(args...) = new(collect(args[1:end-1]), args[end])
end

SymbolicUtils.istree(ex::Exists) = true
SymbolicUtils.operation(ex::Exists) = Exists
SymbolicUtils.arguments(ex::Exists) = [ex.idxs;[ex.arg]]

const QuantifierAsymptote = Union{Forall, Exists}

function show_asymptote_undelimited(io::IO, mime::MIME"text/plain", ex::QuantifierAsymptote)
    print(io, "(")
    show_asymptote(io, mime, ex)
    print(io, ")")
end

function show_asymptote(io::IO, mime::MIME"text/plain", ex::QuantifierAsymptote)
    op(::Forall) = "∀ "
    op(::Exists) = "∃ "
    print(op(ex))
    for idx in ex.idxs[1:end-1]
        show_asymptote(io, mime, idx)
        print(io, ", ")
    end
    if length(ex.idxs) >= 1
        show_asymptote(io, mime, last(ex.idxs))
    end
    print(io, " | ")
    show_asymptote_undelimited(io, mime, ex.arg)
end

struct Times <: AsymptoteNode
    args::Vector{Any}
    Times(args...) = new(collect(args))
end

bases(ex::Times) = mapreduce(bases, vcat, ex.args)

SymbolicUtils.istree(ex::Times) = true
SymbolicUtils.operation(ex::Times) = Times
SymbolicUtils.arguments(ex::Times) = ex.args

struct Cup <: AsymptoteNode
    args::Vector{Any}
    Cup(args...) = new(collect(args))
end

bases(ex::Cup) = mapreduce(bases, vcat, ex.args)

SymbolicUtils.istree(ex::Cup) = true
SymbolicUtils.operation(ex::Cup) = Cup
SymbolicUtils.arguments(ex::Cup) = ex.args

struct Cap <: AsymptoteNode
    args::Vector{Any}
    Cap(args...) = new(collect(args))
end

bases(ex::Cap) = mapreduce(bases, vcat, ex.args)

SymbolicUtils.istree(ex::Cap) = true
SymbolicUtils.operation(ex::Cap) = Cap
SymbolicUtils.arguments(ex::Cap) = ex.args

struct Vee <: AsymptoteNode
    args::Vector{Any}
    Vee(args...) = new(collect(args))
end

SymbolicUtils.istree(ex::Vee) = true
SymbolicUtils.operation(ex::Vee) = Vee
SymbolicUtils.arguments(ex::Vee) = ex.args

struct Wedge <: AsymptoteNode args::Vector{Any}
    Wedge(args...) = new(collect(args))
end

SymbolicUtils.istree(ex::Wedge) = true
SymbolicUtils.operation(ex::Wedge) = Wedge
SymbolicUtils.arguments(ex::Wedge) = ex.args

const BinaryAsymptote = Union{Times, Cup, Cap, Vee, Wedge}

function show_asymptote_undelimited(io::IO, mime::MIME"text/plain", ex::BinaryAsymptote)
    print(io, "(")
    show_asymptote(io, mime, ex)
    print(io, ")")
end

function show_asymptote(io::IO, mime::MIME"text/plain", ex::BinaryAsymptote)
    op(::Times) = " × "
    op(::Cup) = " ∪ \n"
    op(::Cap) = " ∩ "
    op(::Vee) = " ∨ "
    op(::Wedge) = " ∧ "
    for arg in ex.args[1:end-1]
        show_asymptote_undelimited(io, mime, arg)
        print(op(ex))
    end
    if length(ex.args) > 1
        show_asymptote_undelimited(io, mime, last(ex.args))
    elseif length(ex.args) == 1
        show_asymptote(io, mime, last(ex.args))
    elseif length(ex.args) == 0 && ex isa Times
        print(io, "{()}")
    end
end

struct Empty <: AsymptoteNode end

SymbolicUtils.istree(ex::Empty) = false

show_asymptote(io::IO, mime::MIME"text/plain", ex::Empty) = println(io, "∅")

bases(ex::Empty) = []

struct Predicate <: AsymptoteNode
    op
    args
    Predicate(op, args...) = new(op, collect(args))
end

SymbolicUtils.istree(ex::Predicate) = true
SymbolicUtils.operation(ex::Predicate) = Predicate
SymbolicUtils.arguments(ex::Predicate) = [[ex.op];ex.args]

function show_asymptote(io::IO, mime::MIME"text/plain", ex::Predicate)
    show_asymptote(io, mime, ex.op)
    print("[")
    for arg in ex.args[1:end-1]
        show_asymptote(io, mime, arg)
        print(", ")
    end
    if length(ex.args) >= 1
        show_asymptote(io, mime, last(ex.args))
    end
    print("]")
end

struct Such <: AsymptoteNode
    tgt
    prd
    Such(tgt, prd) = new(tgt, prd)
end

bases(ex::Predicate) = bases(ex.prd)

SymbolicUtils.istree(ex::Such) = true
SymbolicUtils.operation(ex::Such) = Such
SymbolicUtils.arguments(ex::Such) = [ex.tgt, ex.prd]

function show_asymptote(io::IO, mime::MIME"text/plain", ex::Such)
    print("{")
    show_asymptote(io, mime, ex.tgt)
    print(" | ")
    show_asymptote(io, mime, ex.prd)
    print("}")
end

function show_asymptote(io::IO, mime::MIME"text/plain", ex)
    print(io, ex)
end

function indices(x::AsymptoteNode)
    return mapreduce(indices, union, arguments(x))
end
indices(x::Forall) = setdiff(indices(x.arg), x.idxs)
indices(x::Exists) = setdiff(indices(x.arg), x.idxs)
indices(x::Predicate) = x.args