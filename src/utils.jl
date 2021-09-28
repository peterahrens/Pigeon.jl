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

macro capture(ex, lhs)
    keys = Symbol[]
    lhs_term = SymbolicUtils.makepattern(lhs, keys)
    unique!(keys)
    bind = Expr(:block, map(key-> :($(esc(key)) = getindex(__MATCHES__, $(QuoteNode(key)))), keys)...)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        __MATCHES__ = SymbolicUtils.Rule($(QuoteNode(lhs)),
             lhs_pattern,
             SymbolicUtils.matcher(lhs_pattern),
             identity,
             SymbolicUtils.rule_depth($lhs_term))($(esc(ex)))
        if __MATCHES__ !== nothing
            $bind
            true
        else
            false
        end
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