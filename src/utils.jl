macro identity(ex) ex end

macro ex(ex)
    @assert ex.head == :macrocall && length(ex.args) >= 1
    if length(ex.args) > 1
        return esc(Expr(:macrocall, ex.args[1], map(arg->macroexpand(__module__, arg, recursive=true), ex.args[2:end])...))
    end
end

macro ex1(ex)
    @assert ex.head == :macrocall && length(ex.args) >= 1
    if length(ex.args) > 1
        return esc(Expr(:macrocall, ex.args[1], map(arg->macroexpand1(__module__, arg, recursive=false), ex.args[2:end])...))
    end
end

variproduct(args) = map(collect, product(args...))
#function variproduct(args)
#    if length(args) == 0
#        return [[]]
#    else
#        [[[head]; tail] for (head, tail) in product(args[1], variproduct(args[2:end]))]
#    end
#end

struct PassThroughSaturate{C}
    rw::C
end

(p::PassThroughSaturate{C})(x) where {C} = (y=p.rw(x); y === nothing ? [x] : [x; y])

struct ChainSaturate{C}
    rws::C
end

function (p::ChainSaturate{C})(x) where {C}
    terms = Any[x]
    for rw in p.rws
        y = rw(x)
        if y !== nothing
            append!(terms, y)
        end
    end
    return terms
end

struct PostwalkSaturate{C}
    rw::C
end

function (p::PostwalkSaturate{C})(x) where {C}
    if istree(x)
        terms = []
        for args in variproduct(map(p, arguments(x)))
            append!(terms, p.rw(similarterm(x, operation(x), args)))
        end
        return terms
    else
        return p.rw(x)
    end
end

struct PrewalkSaturate{C}
    rw::C
end

function (p::PrewalkSaturate{C})(x) where {C}
    terms = []
    for y in p.rw(x)
        if istree(y)
            for args in variproduct(map(p, arguments(y)))
                push!(terms, similarterm(y, operation(y), args))
            end
        else
            push!(terms, y)
        end
    end
    return terms
end

struct FixpointSaturate{C}
    rw::C
end

function (p::FixpointSaturate{C})(x) where {C}
    n = 1
    terms = Set(collect(p.rw(x)))
    result = collect(terms)
    while length(terms) > n
        n = length(terms)
        result = collect(terms)
        for term in result
            union!(terms, p.rw(term))
        end
    end
    return result
end

struct Prestep{C}
    rw::C
end

function (p::Prestep{C})(x) where {C}
    y = p.rw(x)
    if y !== nothing
        if istree(y)
            return similarterm(y, operation(y), map(p, arguments(y)))
        else
            return y
        end
    else
        return x
    end
end

struct Link{C}
    rws::C
end

function (p::Link{C})(x) where {C}
    trigger = false
    for rw in p.rws
        y = rw(x)
        if y !== nothing
            trigger = true
            x = y
        end
    end
    if trigger
        return x
    end
end

"""
sympermutations(v)

Generate all σ such that v[σ] == v and isunique(σ).
"""
sympermutations(v) = sympermutations(v, v)

"""
sympermutations(u, v)

Generate all σ such that u[σ] == v and isunique(σ).
"""
function sympermutations(u, v)
    σs = []
    uu = unique(v)
    for groups in product(map(k->(permutations(findall(isequal(k), u), count(isequal(k), v))), uu)...)
        σ = collect(1:length(v))
        for (group, k) in zip(groups, uu)
            for (i, j) in zip(findall(isequal(k), v), group)
                σ[i] = j
            end
        end
        push!(σs, σ)
    end
    return σs 
end

# unzip

"""
    unzip(itrs) -> NTuple{length(first(itrs)), Vector}
The `unzip` function takes an iterator of iterators and returns a tuple of
vectors such that the first vector contains the first element yielded by each
iterator, the second vector the second element yielded by each iterator, etc.
`unzip` is sort of an inverse to the `zip` operation, as the name suggests.
In particular, if we define
    ≐(a, b) = collect(collect.(a)) == collect(collect.(b))
then the following identities relating `zip` and `unzip` hold for any `itrs`
that is is an iterator of iterators:
    unzip(zip(itrs...)) ≐ itrs
    zip(unzip(itrs)...) ≐ itrs
Note that `unzip` does not return an iterator: it always consumes all of
its argument and all of each iterator yielded by its argument. It is only
associated with iteration because it is the inverse of `zip`.
# Examples
```jldoctest
julia> unzip(enumerate("Hello"))
([1, 2, 3, 4, 5], ['H', 'e', 'l', 'l', 'o'])
julia> unzip([[1, "apple"], [2.5, "orange"], [0, "mango"]])
(Real[1, 2.5, 0], ["apple", "orange", "mango"])
```
"""
function unzip(itrs)
    n = Base.haslength(itrs) ? length(itrs) : nothing
    outer = iterate(itrs)
    outer === nothing && return ()
    vals, state = outer
    vecs = ntuple(length(vals)) do i
        x = vals[i]
        v = Vector{typeof(x)}(undef, something(n, 1))
        @inbounds v[1] = x
        return v
    end
    unzip_rest(vecs, typeof(vals), n isa Int ? 1 : nothing, itrs, state)
end

function unzip_rest(vecs, eltypes, i, itrs, state)
    while true
        i isa Int && (i += 1)
        outer = iterate(itrs, state)
        outer === nothing && return vecs
        itr, state = outer
        vals = Tuple(itr)
        if vals isa eltypes
            for (v, x) in zip(vecs, vals)
                if i isa Int
                    @inbounds v[i] = x
                else
                    push!(v, x)
                end
            end
        else
            vecs′ = map(vecs, vals) do v, x
                T = Base.promote_typejoin(eltype(v), typeof(x))
                v′ = Vector{T}(undef, length(v) + !(i isa Int))
                copyto!(v′, v)
                @inbounds v′[something(i, end)] = x
                return v′
            end
            eltypes′ = Tuple{map(eltype, vecs′)...}
            return unzip_rest(Tuple(vecs′), eltypes′, i, itrs, state)
        end
    end
end