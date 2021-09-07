mutable struct PointQuery
    points
end

struct CanonVariable
    n
end

function Base.getindex(q::PointQuery, idxs...)
    d = Dict(args...)
    rename(x::CanonVariable) = haskey(d, x.n) ? d[x.n] : x
    rename(x) = x
    PostWalk(rename)(q.points)
end

function Base.setindex!(q::PointQuery, p, idxs...)
    d = Dict(args...)
    rename(x) = haskey(d, x) ? CanonVariable(d[x]) : x
    q.points = Vee(q.points, PostWalk(rename)(p))
end

mutable struct SparseFiberRelation
    data::PointQuery
    format
    default
    implicit
end

initialize(tns::SparseFiberRelation) = (tns.data = PointQuery(false))
implicitize(tns::SparseFiberRelation) = (tns = copy(tns); tns.data = PointQuery(false); tns)

struct CoiterateRelator end
struct LocateRelator end

mutable struct AsymptoticContext
    itrs::Any
    qnts::Vector{Any}
    guards::Vector{Any}
end
AsymptoticContext() = AsymptoticContext([], true)

function iterate!(ctx)
    axes_pred = Wedge(map(qnt->Predicate(ctx.axes[qnt], getname(qnt)), ctx.qnts)...)
    guard_pred = Wedge(ctx.guard...)
    ctx.itrs = Cup(ctx.itrs, Such(Times(getname.(ctx.qnts)...), Wedge(axes_pred, guard_pred)))
end

quantify(f, ctx, var) = (push!(ctx.qnts, var); f(); pop!(ctx.qnts))
enguard(f, ctx, cond) = (push!(ctx.grds, cond); f(); pop!(ctx.grds))
guard(ctx) = reduce(Wedge, ctx.grds)

lower!(::Pass, ::AsymptoticContext, ::DefaultStyle) = nothing

#assumes unique foralls
function lower!(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
end


function lower(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return lower(stmt.body, ctx)
    quantify(ctx, stmt.idxs[1]) do
        lower!(Loop(stmt.idxs[2:end], stmt.body), quantify(ctx, stmt.idxs[1]))
    end
end

function lower!(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    lower!(stmt.prod, ctx)
    lower!(stmt.cons, ctx)
end

struct CoiterateStyle
    style
end

#TODO handle children of access?
make_style(root::Loop, ctx::AsymptoticContext, node::Access{SymbolicCoiterableTensor}) =
    (!isempty(root.idxs) && root.idxs[1] in node.idxs) ? CoiterateStyle(DefaultStyle()) : DefaultStyle()
combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle(result_style(a.style, b.style))

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
        coiterate_asymptote!(stmt, ctx, stmt′)
        cases = coiterate_cases(stmt, ctx, stmt′)
        body_iters, body_binds = mapreduce(lower_asymptote_merge, cases) do (guard, body)
            enguard(ctx, guard) do
                lower!(annihilate_index(body), ctx)
            end
        end
    end
    return (Cup(loop_iters, body_iters), body_binds)
end

function coiterate_asymptote!(root, ctx, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote(root, ctx, arg), Cup, arguments(node))
    else
        return Empty()
    end
end
function coiterate_asymptote!(root, ctx, stmt::Access{SymbolicCoiterableTensor})
    root.idxs[1] in stmt.idxs || return Empty()
    pred = Exists(getname.(setdiff(idxs, ctx.qnts))..., stmt.tns.data[stmt.idxs...])
    return Such(Times(getname.(ctx.qnts)...), pred)
end

function coiterate_cases(root, ctx, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(root, ctx, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(ctx.guard, node),]
    end
end
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Access{SymbolicCoiterableTensor})
    if !isempty(stmt.idxs) && root.idxs[1] in stmt.idxs
        stmt′ = stmt.mode === Read() ? stmt.tns.default : Access(implicitize(stmt.tns), stmt.mode, stmt.idxs)
        pred = Exists(getname.(setdiff(idxs, ctx.qnts))..., stmt.tns.data[stmt.idxs...])
        return [(pred, stmt),
            (ctx.guard, stmt′),]
    else
        return [(ctx.guard, stmt),]
    end
end

function lower!(root::Assign{<:Access{SparseFiberRelation}}, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
    pred = Exists(setdiff(ctx.qnts, root.lhs.idxs)..., ctx.guard)
    root.lhs.tns.data[root.lhs.idxs...] = pred
end