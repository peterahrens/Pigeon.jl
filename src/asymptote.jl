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

TermInterface.istree(::Type{<:Forall}) = true
TermInterface.operation(ex::Forall) = Forall
TermInterface.arguments(ex::Forall) = [ex.idxs;[ex.arg]]

struct Exists <: AsymptoteNode
    idxs::Vector{Any}
    arg::Any
    Exists(args...) = new(collect(args[1:end-1]), args[end])
end

TermInterface.istree(::Type{<:Exists}) = true
TermInterface.operation(ex::Exists) = Exists
TermInterface.arguments(ex::Exists) = [ex.idxs;[ex.arg]]

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

TermInterface.istree(::Type{<:Times}) = true
TermInterface.operation(ex::Times) = Times
TermInterface.arguments(ex::Times) = ex.args

struct Cup <: AsymptoteNode
    args::Vector{Any}
    Cup(args...) = new(collect(args))
end

bases(ex::Cup) = mapreduce(bases, vcat, ex.args)

TermInterface.istree(::Type{<:Cup}) = true
TermInterface.operation(ex::Cup) = Cup
TermInterface.arguments(ex::Cup) = ex.args

struct Cap <: AsymptoteNode
    args::Vector{Any}
    Cap(args...) = new(collect(args))
end

bases(ex::Cap) = mapreduce(bases, vcat, ex.args)

TermInterface.istree(::Type{<:Cap}) = true
TermInterface.operation(ex::Cap) = Cap
TermInterface.arguments(ex::Cap) = ex.args

struct Vee <: AsymptoteNode
    args::Vector{Any}
    Vee(args...) = new(collect(args))
end

TermInterface.istree(::Type{<:Vee}) = true
TermInterface.operation(ex::Vee) = Vee
TermInterface.arguments(ex::Vee) = ex.args

struct Wedge <: AsymptoteNode args::Vector{Any}
    Wedge(args...) = new(collect(args))
end

TermInterface.istree(::Type{<:Wedge}) = true
TermInterface.operation(ex::Wedge) = Wedge
TermInterface.arguments(ex::Wedge) = ex.args

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

TermInterface.istree(::Type{<:Empty}) = false

show_asymptote(io::IO, mime::MIME"text/plain", ex::Empty) = println(io, "∅")

bases(ex::Empty) = []

struct Predicate <: AsymptoteNode
    op
    args
    Predicate(op, args...) = new(op, collect(args))
end

TermInterface.istree(::Type{<:Predicate}) = true
TermInterface.operation(ex::Predicate) = Predicate
TermInterface.arguments(ex::Predicate) = [[ex.op]; ex.args]

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

TermInterface.istree(::Type{<:Such}) = true
TermInterface.operation(ex::Such) = Such
TermInterface.arguments(ex::Such) = [ex.tgt, ex.prd]

function show_asymptote(io::IO, mime::MIME"text/plain", ex::Such)
    print("{")
    show_asymptote(io, mime, ex.tgt)
    print(" | ")
    show_asymptote(io, mime, ex.prd)
    print("}")
end

function show_asymptote(io::IO, mime::MIME"text/plain", ex)
    show(io, mime, ex)
end

function indices(x::AsymptoteNode)
    return mapreduce(indices, union, arguments(x))
end
indices(x::Forall) = setdiff(indices(x.arg), x.idxs)
indices(x::Exists) = setdiff(indices(x.arg), x.idxs)
indices(x::Predicate) = x.args

simplify_asymptote = Fixpoint(Postwalk(Chain([
    (@rule Such(Such(~s, ~p), ~q) => Such(~s, Wedge(~p, ~q))),

    (@rule Such(~s, false) => Empty()),
    (@rule Such($(Empty()), ~p) => Empty()),

    (@rule Wedge(~~p, Wedge(~~q), ~~r) => Wedge(~~p..., ~~q..., ~~r...)),
    (@rule Wedge(~~p, true, ~q, ~~r) => Wedge(~~p..., ~q, ~r...)),
    (@rule Wedge(~~p, ~q, true, ~~r) => Wedge(~~p..., ~q, ~r...)),
    (@rule Wedge(true) => true),
    (@rule Wedge(~~p, false, ~q, ~~r) => false),
    (@rule Wedge(~~p, ~q, false, ~~r) => false),
    (@rule Wedge(~~p, ~q, ~~r, ~q, ~~s) => Wedge(~~p..., ~q, ~~r..., ~~s...)),

    (@rule Vee(~p) => ~p),

    (@rule Wedge(~~p, Vee(~q, ~r, ~~s), ~~t) => 
        Vee(Wedge(~~p..., ~q, ~~t...), Wedge(~~p..., Vee(~r, ~~s...), ~~t...))),

    (@rule Cup(~~s, $(Empty()), ~t, ~~u) => Cup(~~s..., ~t, ~~u...)),
    (@rule Cup(~~s, ~t, $(Empty()), ~~u) => Cup(~~s..., ~t, ~~u...)),
    (@rule Cup($(Empty())) => Empty()),
    (@rule Cup(~~s, Cup(~~t), ~~u) => Cup(~~s..., ~~t..., ~~u...)),
    (@rule Cup(~~s, ~t, ~~u, ~t, ~~v) => Cup(~~s..., ~t, ~~u..., ~~v...)),

    (@rule Cap(~~s, $(Empty()), ~~u) => Empty()),
    (@rule Cap(~s) => ~s),

    (@rule Times(~~s, $(Empty()), ~~u) => Empty()),
    (@rule Times(~~s, Times(~~t), ~~u) => Times(~~s..., ~~t..., ~~u...)),
    (@rule Times(Such(~s, ~p), ~~t) => Such(Times(~s, ~~t...), ~p)),
    (@rule Times(Cup(~s, ~t, ~~u), ~~v) => Cup(Times(~s, ~~v...), Times(Cup(~t, ~~u...), ~~v...))),
    (@rule Times(Cup(~s), ~~t) => Cup(Times(~s), ~~t...)),

    (@rule Such(~t, true) => ~t),
    (@rule Such(~t, Vee(~p, ~q)) => 
        Cup(Such(~t, ~p), Such(~t, ~q))),
    (@rule Such(Cup(~s, ~t, ~~u), ~p) => 
        Cup(Such(~s, ~p), Such(Cup(~t, ~~u...), ~p))),
    (@rule Such(Cup(~s), ~p) => Cup(Such(~s, ~p))),
    (@rule Cap(~~s, Such(~t, ~p), ~~u, Such(~t, ~q), ~~v) =>
        Cap(~~s..., Such(~t, Wedge(~p, ~q)), ~~u..., ~~v...)),

    (@rule Exists(~~i, true) => true),
    (@rule Exists(~~i, false) => false),
    (@rule Exists(~p) => ~p),
    (@rule Exists(~~i, Exists(~~j, ~p)) => Exists(~~i..., ~~j..., ~p)),
    (@rule Wedge(~~p, Exists(~~i, ~q), ~~r) => begin
        i′ = freshen.(~~i)
        q′ = Postwalk(subex->get(Dict(Pair.(~~i, i′)...), subex, subex))(~q)
        Exists(i′..., Wedge(~~p..., q′, ~~r...))
    end),
    (@rule Exists(~~i, ~p) => if !isempty(setdiff(~~i, indices(~p)))
        Exists(intersect(~~i, indices(~p))..., ~p)
    end),

    (@rule Exists(~~i, Vee(~p, ~q, ~~r)) =>
        Vee(Exists(~~i, ~p), Exists(~~i, Vee(~q, ~~r)))),
])))

mutable struct PointQuery
    points
end

struct CanonVariable
    n
end

function Base.getindex(q::PointQuery, idxs...)
    d = Dict(enumerate(map(getname, idxs)))
    rename(x::CanonVariable) = haskey(d, x.n) ? d[x.n] : x
    rename(x) = x
    Postwalk(rename)(q.points)
end

function Base.setindex!(q::PointQuery, p, idxs...)
    d = Dict(reverse.(enumerate(map(getname, idxs))))
    rename(x) = haskey(d, x) ? CanonVariable(d[x]) : x
    q.points = Vee(q.points, Postwalk(rename)(p))
    q[idxs...]
end