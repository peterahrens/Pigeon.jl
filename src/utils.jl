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

struct PassThroughStep{C}
    rw::C
end

(p::PassThroughStep{C})(x) where {C} = (y=p.rw(x); y === nothing ? [x] : [x; y])

struct ChainStep{C}
    rws::C
end

function (p::ChainStep{C})(x) where {C}
    terms = Any[x]
    for rw in p.rws
        y = rw(x)
        if y !== nothing
            append!(terms, y)
        end
    end
    return terms
end

struct PostwalkStep{C}
    rw::C
end

function (p::PostwalkStep{C})(x) where {C}
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

struct PrewalkStep{C}
    rw::C
end

function (p::PrewalkStep{C})(x) where {C}
    if istree(x)
        terms = []
        for y in p.rw(x)
            for args in variproduct(map(p, arguments(y)))
                push!(terms, similarterm(y, operation(y), args))
            end
        end
        return terms
    else
        return p.rw(x)
    end
end

struct FixpointStep{C}
    rw::C
end

function (p::FixpointStep{C})(x) where {C}
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

function sympermutations(v)
    σs = []
    for groups in product(map(i->permutations(findall(i, v)), unique(v))...)
        σ = collect(1:length(v))
        for group in groups
            for (i, j) in zip(sort(group), group)
                σ[i] = j
            end
        end
        push!(σs, σ)
    end
end

function sympermutations(u, v)
    return map(σ -> u[σ], sympermutations(v))
end