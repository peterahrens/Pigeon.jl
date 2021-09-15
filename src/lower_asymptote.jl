mutable struct SparseFiberRelation
    name
    format
    dims
    default
    implicit
end
Base.copy(tns::SparseFiberRelation) = SparseFiberRelation(
    tns.name,
    tns.format,
    tns.dims,
    tns.default,
    tns.implicit)

#TODO this type probably needs a rework, but we will wait till we see what the enumerator needs
SparseFiberRelation(name, format, dims) = SparseFiberRelation(name, format, dims, Literal(0))
SparseFiberRelation(name, format, dims, default) = SparseFiberRelation(name, format, dims, default, false)


getname(tns::SparseFiberRelation) = tns.name
rename(tns::SparseFiberRelation, name) = (tns = Base.copy(tns); tns.name = name; tns)

const Fiber = SparseFiberRelation

initialize(tns::SparseFiberRelation) = (tns.data = PointQuery(false))
implicitize(tns::SparseFiberRelation) = (tns = copy(tns); tns.implicit = true; tns)

struct CoiterateRelator end
struct LocateRelator end

const coiter = CoiterateRelator()
const locate = LocateRelator()

mutable struct AsymptoticContext
    itrs::Any
    qnts::Vector{Any}
    guards::Vector{Any}
    state::Dict
    dims
end

function getdata(tns::SparseFiberRelation, ctx::AsymptoticContext)
    default = PointQuery(Predicate(getname(tns), [CanonVariable(n) for n in 1:length(tns.format)]...))
    get!(ctx.state, getname(tns), default)
end

lower_axes(tns::SparseFiberRelation, ::AsymptoticContext) = tns.dims
lower_axis_merge(::AsymptoticContext, a, b) = (@assert a == b; b)

AsymptoticContext() = AsymptoticContext(Empty(), [], [true], Dict(), Dimensions())

getdims(ctx::AsymptoticContext) = ctx.dims

function asymptote(prgm)
    #TODO messy
    prgm = transform_ssa(prgm)
    ctx = AsymptoticContext()
    lower!(prgm, ctx)
    return ctx.itrs
end

iterate!(ctx) = iterate!(ctx, true)
function iterate!(ctx, cond)
    axes_pred = Wedge(map(qnt->Predicate(ctx.dims[getname(qnt)], getname(qnt)), ctx.qnts)...)
    ctx.itrs = Cup(ctx.itrs, Such(Times(getname.(ctx.qnts)...), Wedge(axes_pred, guard(ctx), cond)))
end

quantify(f, ctx, var) = (push!(ctx.qnts, var); f(); pop!(ctx.qnts))
enguard(f, ctx, cond) = (push!(ctx.guards, cond); f(); pop!(ctx.guards))
guard(ctx) = reduce(Wedge, ctx.guards)

lower!(::Pass, ::AsymptoticContext, ::DefaultStyle) = nothing

#assumes unique foralls
function lower!(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
end

function lower!(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return lower!(stmt.body, ctx)
    quantify(ctx, stmt.idxs[1]) do
        lower!(Loop(stmt.idxs[2:end], stmt.body), ctx)
    end
end

function lower!(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    initialize!(getresult(stmt.prod), ctx)
    lower!(stmt.prod, ctx)
    lower!(stmt.cons, ctx)
end

struct CoiterateStyle
end

#TODO handle children of access?
function make_style(root, ctx::AsymptoticContext, node::Access{SparseFiberRelation})
    isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
    return DefaultStyle()
end

function make_style(root::Loop, ctx::AsymptoticContext, node::Access{SparseFiberRelation})
    isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
    isempty(root.idxs) && return DefaultStyle()
    i = findfirst(isequal(root.idxs[1]), node.idxs)
    (i !== nothing && node.idxs[1:i-1] ⊆ ctx.qnts) || return DefaultStyle()
    node.tns.format[i] === coiter || return DefaultStyle()
    return CoiterateStyle()
end
combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle()
combine_style(a::CoiterateStyle, b::DimensionalizeStyle) = DimensionalizeStyle()
combine_style(a::DefaultStyle, b::DimensionalizeStyle) = DimensionalizeStyle()
combine_style(a::DimensionalizeStyle, b::DimensionalizeStyle) = DimensionalizeStyle()

#TODO generalize the interface to annihilation analysis
annihilate_index = Fixpoint(Postwalk(Chain([
    (@ex@rule i"(~f)(~~a)"p => if isliteral(~f) && all(isliteral, ~~a) Literal(value(~f)(value.(~~a)...)) end),
    (@ex@rule i"+(~~a, +(~~b), ~~c)"p => i"+(~~a, ~~b, ~~c)"c),
    (@ex@rule i"+(~~a)"p => if any(isliteral, ~~a) i"+($(filter(!isliteral, ~~a)), $(Literal(+(value.(filter(isliteral, ~~a))...))))"c end),
    (@ex@rule i"+(~~a, 0, ~~b)"p => i"+(~~a, ~~b)"c),

    (@ex@rule i"*(~~a, *(~~b), ~~c)"p => i"*(~~a, ~~b, ~~c)"c),
    (@ex@rule i"*(~~a)"p => if any(isliteral, ~~a) i"*($(filter(!isliteral, ~~a)), $(Literal(*(value.(filter(isliteral, ~~a))...))))"c end),
    (@ex@rule i"*(~~a, 1, ~~b)"p => i"*(~~a, ~~b)"c),
    (@ex@rule i"*(~~a, 0, ~~b)"p => Literal(0)),

    (@ex@rule i"+(~a)"p => ~a),
    (@ex@rule i"~a - ~b"p => i"~a + - ~b"c),
    (@ex@rule i"- (- ~a)"p => ~a),
    (@ex@rule i"- +(~a, ~~b)"p => i"+(- ~a, - +(~~b))"c),
    (@ex@rule i"*(~a)"p => ~a),
    (@ex@rule i"*(~~a, - ~b, ~~c)"p => i"-(*(~~a, ~b, ~~c))"c),

    #(@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
    #(@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)

    (@ex@rule i"(~a)[~~i] = 0"p => Pass()), #TODO this is only valid when the default of A is 0
    (@ex@rule i"(~a)[~~i] += 0"p => Pass()),
    (@ex@rule i"(~a)[~~i] *= 1"p => Pass()),

    (@ex@rule i"(~a)[~~i] *= ~b"p => if isimplicit(~a) && (~a).default == Literal(0) Pass() end),
    (@ex@rule i"(~a)[~~i] = ~b"p => if isimplicit(~a) && (~a).default == ~b Pass() end),

    (@ex@rule i"∀ (~~i) $(Pass())"p => Pass()),
    (@ex@rule i"$(Pass()) with $(Pass())"p => Pass()),
])))

function lower!(stmt::Loop, ctx::AsymptoticContext, ::CoiterateStyle)
    isempty(stmt.idxs) && return ctx(stmt.body)
    quantify(ctx, stmt.idxs[1]) do
        stmt′ = Loop(stmt.idxs[2:end], stmt.body)
        cases = coiterate_cases(stmt, ctx, stmt′)
        for (guard, body) in cases
            enguard(ctx, guard) do
                lower!(annihilate_index(body), ctx)
            end
        end
        coiterate_asymptote!(stmt, ctx, stmt′)
    end
end

function coiterate_asymptote!(root, ctx, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote!(root, ctx, arg), Cup, arguments(node))
    else
        return Empty()
    end
end

function coiterate_asymptote!(root, ctx, stmt::Access{SparseFiberRelation})
    i = findfirst(isequal(root.idxs[1]), stmt.idxs)
    (i !== nothing && stmt.idxs[1:i] ⊆ ctx.qnts) || return Empty()
    stmt.tns.format[i] === coiter || return Empty() #TODO this line isn't extensible
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs...])
    return iterate!(ctx, pred)
end

function coiterate_cases(root, ctx, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(root, ctx, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(true, node),]
    end
end
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Access{SparseFiberRelation})
    single = [(true, stmt),]
    i = findfirst(isequal(root.idxs[1]), stmt.idxs)
    (i !== nothing && stmt.idxs[1:i] ⊆ ctx.qnts) || return single
    stmt.tns.format[i] === coiter || return single
    stmt′ = stmt.mode === Read() ? stmt.tns.default : Access(implicitize(stmt.tns), stmt.mode, stmt.idxs)
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs...])
    return [(pred, stmt), (true, stmt′),]
end

function lower!(root::Assign{<:Access{SparseFiberRelation}}, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
    pred = Exists(getname.(setdiff(ctx.qnts, root.lhs.idxs))..., guard(ctx))
    getdata(root.lhs.tns, ctx)[root.lhs.idxs...] = pred
end

function initialize!(tns::SparseFiberRelation, ctx::AsymptoticContext)
    ctx.state[getname(tns)] = PointQuery(false)
end

function filter_pareto(kernels)
    pareto = []
    asymptotes = map(kernel->simplify_asymptote(asymptote(kernel)), kernels)
    for (a, asy_a) in zip(kernels, asymptotes)
        keep = true
        for (b, asy_b) in zip(kernels, asymptotes)
            if (isdominated(asy_b, asy_a)) && !(isdominated(asy_a, asy_b))
                keep = false
                break
            end
        end
        if keep
            push!(pareto, a)
        end
    end
    return pareto
end
