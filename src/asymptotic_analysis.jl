struct SymbolicCoiterableTensor
    name
    default
    implicit #describes whether this tensor initially holds entirely implicit values
end
name(tns::SymbolicCoiterableTensor) = tns.name
SCTensor(name) = SCTensor(name, Literal(0))
SCTensor(name, default) = SymbolicCoiterableTensor(name, default, false)
isimplicit(tns::SymbolicCoiterableTensor) = tns.implicit
implicitize(tns::SymbolicCoiterableTensor) = SymbolicCoiterableTensor(tns.name, tns.default, true)

struct SymbolicLocateTensor
    name
end
name(tns::SymbolicLocateTensor) = tns.name
SLTensor(name) = SymbolicLocateTensor(name)

isimplicit(x) = false

#pass in a guard on the iteration
#return the iteration and whatever information should be gleaned from the assignments

struct AsymptoticContext
    qnts::Set{Any}
    bindings::Dict{Any}
    guard::Any
end
AsymptoticContext() = AsymptoticContext(Set(), Dict(), true)

quantify(ctx::AsymptoticContext, vars...) = AsymptoticContext(union(ctx.qnts, vars), ctx.bindings, ctx.guard)
bind(ctx::AsymptoticContext, vars) = AsymptoticContext(ctx.qnts, merge(lower_asymptote_bind_merge, ctx.bindings, vars), ctx.guard)
enguard(ctx::AsymptoticContext, guard) = AsymptoticContext(ctx.qnts, ctx.bindings, Wedge(ctx.guard, guard))

lower_asymptote_merge((iters_a, bindings_a), (iters_b, bindings_b)) =
    (Cup(iters_a, iters_b), merge(lower_asymptote_bind_merge, bindings_a, bindings_b))

lower(::Pass, ::AsymptoticContext, ::DefaultStyle) = (Empty(), Dict())

function lower(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    return (Such(Times(name.(ctx.qnts)...), ctx.guard), Dict())
end

function lower(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return lower(stmt.body, ctx)
    return lower(Loop(stmt.idxs[2:end], stmt.body), quantify(ctx, stmt.idxs[1]))
end

function lower(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    prod_iters, prod_bindings = lower(stmt.prod, ctx)
    cons_iters, cons_bindings = lower(stmt.cons, bind(ctx, prod_bindings))
    println(prod_bindings)
    return (Cup(prod_iters, cons_iters), cons_bindings)
end

struct CoiterateStyle
    style
    verified
end

make_style(root::Loop, ctx::AsymptoticContext, node::SymbolicCoiterableTensor) = CoiterateStyle(DefaultStyle(), false)
resolve_style(root::Loop, ctx::AsymptoticContext, node::Access, style::CoiterateStyle) =
    ((!isempty(root.idxs) && root.idxs[1] in node.idxs) || style.verified) ? CoiterateStyle(style.style, true) :
        resolve_style(root, ctx, node, style.style)
combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle(result_style(a.style, b.style), a.verified | b.verified)

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

function lower(stmt::Loop, ctx::AsymptoticContext, ::CoiterateStyle)
    isempty(stmt.idxs) && return ctx(stmt.body)
    ctx′ = quantify(ctx, stmt.idxs[1])
    stmt′ = Loop(stmt.idxs[2:end], stmt.body)
    loop_iters = coiterate_asymptote(stmt, ctx′, stmt′)
    cases = coiterate_cases(stmt, ctx′, stmt′)
    body_iters, body_binds = mapreduce(lower_asymptote_merge, cases) do (guard, body)
            lower(annihilate_index(body), enguard(ctx′, guard))
    end
    return (Cup(loop_iters, body_iters), body_binds)
end

coiterate_asymptote(root, ctx, node) = _coiterate_asymptote(root, ctx, node)
function _coiterate_asymptote(root, ctx, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote(root, ctx, arg), Cup, arguments(node))
    else
        return Empty()
    end
end
coiterate_asymptote(root, ctx, stmt::Access) = coiterate_asymptote(root, ctx, stmt, stmt.tns)
coiterate_asymptote(root, ctx, stmt, tns) = _coiterate_asymptote(root, ctx, stmt)
function coiterate_asymptote(root, ctx, stmt, tns::SymbolicCoiterableTensor)
    root.idxs[1] in stmt.idxs || return Empty()
    return Such(Times(name.(ctx.qnts)...), coiterate_predicate(ctx, tns, stmt.idxs))
end

coiterate_cases(root, ctx, node) = _coiterate_cases(root, ctx, node)
struct _coiterate_processed arg end
coiterate_cases(root, ctx::AsymptoticContext, node::_coiterate_processed) = [(ctx.guard, node.arg)]
function _coiterate_cases(root, ctx, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(root, ctx, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(ctx.guard, node),]
    end
end
coiterate_cases(root, ctx, stmt::Access) = coiterate_cases(root, ctx, stmt::Access, stmt.tns)
coiterate_cases(root, ctx, stmt::Access, tns) = _coiterate_cases(root, ctx, stmt)
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Access, tns::SymbolicCoiterableTensor)
    if !isempty(stmt.idxs) && root.idxs[1] in stmt.idxs
        return [(coiterate_predicate(ctx, tns, stmt.idxs), stmt),
            (ctx.guard, tns.default),]
    else
        return [(ctx.guard, stmt),]
    end
end
coiterate_cases(root, ctx, stmt::Assign) = coiterate_cases(root, ctx, stmt::Assign, stmt.lhs.tns)
coiterate_cases(root, ctx, stmt::Assign, tns) = _coiterate_cases(root, ctx, stmt)
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Assign, tns::SymbolicCoiterableTensor)
    stmt′ = Assign(_coiterate_processed(stmt.lhs), stmt.op, stmt.rhs)
    if !isempty(stmt.lhs.idxs) && root.idxs[1] in stmt.lhs.idxs
        stmt′′ = Assign(_coiterate_processed(Access(implicitize(tns), stmt.lhs.idxs)), stmt.op, stmt.rhs)
        ctx′ = enguard(ctx, coiterate_predicate(ctx, tns, stmt.lhs.idxs))
        return vcat(_coiterate_cases(root, ctx′, stmt′), _coiterate_cases(root, ctx, stmt′′))
    else
        return _coiterate_cases(root, ctx, stmt′)
    end
end

#make_style(root::Assign, ctx::AsymptoticContext, node::SymbolicCoiterableTensor) = CoiterateStyle(DefaultStyle(), false)
#function lower(root::Assign, ctx::AsymptoticContext, style::CoiterateStyle)
function lower(root::Assign, ctx::AsymptoticContext, style::DefaultStyle)
    return (Such(Times(name.(ctx.qnts)...), ctx.guard), coiterate_bind(root, ctx, root.lhs.tns))
end
struct BindSite
    n
end
struct SymbolicPattern
    stuff
end
coiterate_predicate(ctx::AsymptoticContext, tns, idxs) = true
function coiterate_predicate(ctx::AsymptoticContext, tns::SymbolicCoiterableTensor, idxs)
    if haskey(ctx.bindings, name(tns))
        rename(n::BindSite) = name(idxs[n.n])
        rename(x) = x
        pattern = Postwalk(PassThrough(rename))(ctx.bindings[name(tns)].stuff)
    else
        pattern = Predicate(name(tns), name.(idxs)...)
    end
    Wedge(ctx.guard, Exists(name.(filter(j->!(j ∈ ctx.qnts), idxs))..., pattern))
end

coiterate_bind(root, ctx, tns) = Dict()
function coiterate_bind(root, ctx, tns::Union{SymbolicCoiterableTensor, SymbolicLocateTensor})
    renamer = Postwalk(PassThrough(idx -> if (n = findfirst(isequal(idx), name.(root.lhs.idxs))) !== nothing BindSite(n) end))
    #TODO doesn't handle A{i, i}
    Dict(name(tns)=>SymbolicPattern(Exists(filter(j->!(j ∈ ctx.qnts), root.lhs.idxs), renamer(ctx.guard))))
end
lower_asymptote_bind_merge(a::SymbolicPattern, b::SymbolicPattern) = SymbolicPattern(Vee(a.stuff, b.stuff))

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