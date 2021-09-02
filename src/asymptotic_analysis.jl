struct SymbolicCoiterableTensor
    name
    default
    implicit #describes whether this tensor initially holds entirely implicit values
end
name(tns::SymbolicCoiterableTensor) = tns.name
SCTensor(name) = SCTensor(name, Literal(0))
SCTensor(name, default) = SymbolicCoiterableTensor(name, default, false)
isimplicit(tns::SymbolicCoiterableTensor) = tns.implicit

struct SymbolicLocateTensor
    name
end
name(tns::SymbolicLocateTensor) = tns.name
SLTensor(name) = SymbolicLocateTensor(name)

isimplicit(x) = false

#pass in a guard on the iteration
#return the iteration and whatever information should be gleaned from the assignments

struct AsymptoticAnalysis
    qnts::Set{Any}
end
AsymptoticAnalysis() = AsymptoticAnalysis(Set())

quantify(lwr::AsymptoticAnalysis, vars...) = AsymptoticAnalysis(union(lwr.qnts, vars))

(lwr::AsymptoticAnalysis)(node) = lwr(node, make_style(lwr, node))

(lwr::AsymptoticAnalysis)(::Pass, ::DefaultStyle) = Empty()

function (lwr::AsymptoticAnalysis)(root::Assign, ::DefaultStyle)
    #at the point when we get to lowering an assign, the lhs had better be a resolvable location
    #(do_assign(resolve(root.lhs), $op, lwr(root.rhs))
    #similarly, at the point when we get to lowering an access, the lhs had better be a resolvable location, otherwise we just resolve it too.
    #assignments allow lhs to put info into scope
    #coiterates will call merge on those scopes, and wheres will call merge on those scopes.
    return Times(name.(lwr.qnts)...)
end

function (lwr::AsymptoticAnalysis)(stmt::Loop, ::DefaultStyle)
    isempty(stmt.idxs) && return lwr(stmt.body)
    quantify(lwr, stmt.idxs[1])(Loop(stmt.idxs[2:end], stmt.body))
end

struct CoiterateStyle
    style
    verified
end

make_style(lwr::AsymptoticAnalysis, root::Loop, node::SymbolicCoiterableTensor) = CoiterateStyle(DefaultStyle(), false)
resolve_style(lwr::AsymptoticAnalysis, root::Loop, node::Access, style::CoiterateStyle) =
    ((!isempty(root.idxs) && root.idxs[1] in node.idxs) || style.verified) ? CoiterateStyle(style.style, true) :
        resolve_style(lwr, root, node, style.style)
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

function (lwr::AsymptoticAnalysis)(stmt::Loop, ::CoiterateStyle)
    isempty(stmt.idxs) && return lwr(stmt.body)
    lwr′ = quantify(lwr, stmt.idxs[1])
    Cup(coiterate_asymptote(lwr′, stmt, stmt),
        mapreduce(Cup, coiterate_cases(lwr′, stmt, Loop(stmt.idxs[2:end], stmt.body))) do (guard, body)
            Such(lwr′(annihilate_index(body)), guard)
        end)
end

coiterate_asymptote(lwr, root, node) = _coiterate_asymptote(lwr, root, node)
function _coiterate_asymptote(lwr, root, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote(lwr, root, arg), Cup, arguments(node))
    else
        return Empty()
    end
end
coiterate_asymptote(lwr, root, stmt::Access) = coiterate_asymptote(lwr, root, stmt, stmt.tns)
coiterate_asymptote(lwr, root, stmt::Access, tns) = _coiterate_asymptote(lwr, root, stmt)
function coiterate_asymptote(lwr, root, stmt::Access, tns::SymbolicCoiterableTensor)
    root.idxs[1] in stmt.idxs || return Empty()
    return Such(Times(name.(lwr.qnts)...), Exists(name.(filter(j->!(j ∈ lwr.qnts), stmt.idxs))...,
                Predicate(name.(arguments(stmt))...)))
end

coiterate_cases(lwr, root, node, write...) = _coiterate_cases(lwr, root, node, write...)
function _coiterate_cases(lwr, root, node, write...)
    if istree(node)
        map(product(map(arg->coiterate_cases(lwr, root, arg, write...), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(true, node),]
    end
end
function _coiterate_cases(lwr, root, node::Assign)
    map(product(coiterate_cases(lwr, root, node.lhs, true), coiterate_cases(lwr, root, node.rhs, false))) do case
        (guards, (lhs_case, rhs_case)) = zip(case...)
        (Wedge(guards...), assign(lhs_case, node.op, rhs_case))
    end
end
coiterate_cases(lwr, root, stmt::Access, write) = coiterate_cases(lwr, root, stmt::Access, write, stmt.tns)
coiterate_cases(lwr, root, stmt::Access, write, tns) = _coiterate_cases(lwr, root, stmt, write)
function coiterate_cases(lwr::AsymptoticAnalysis, root, stmt::Access, write, tns::SymbolicCoiterableTensor)
    stmt′ = Access(SymbolicCoiterableTensor(tns.name, tns.default, true), stmt.idxs)
    if !isempty(stmt.idxs) && root.idxs[1] in stmt.idxs
        return [(Exists(name.(filter(j->!(j ∈ lwr.qnts), stmt.idxs))...,
                Predicate(name.(arguments(stmt))...)), stmt),
            (true, write ? stmt′ : tns.default),]
    else
        return [(true, stmt),]
    end
end

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