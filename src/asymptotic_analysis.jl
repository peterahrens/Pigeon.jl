struct HollowSymbolicTensor
    name
    default
end
name(tns::HollowSymbolicTensor) = tns.name

struct AsymptoticAnalysis
    qnts::Set{Any}
end
AsymptoticAnalysis() = AsymptoticAnalysis(Set())

quantify(lwr::AsymptoticAnalysis, vars...) = AsymptoticAnalysis(union(lwr.qnts, vars))

(lwr::AsymptoticAnalysis)(node) = lwr(node, make_style(lwr, node))

(lwr::AsymptoticAnalysis)(::Pass, ::DefaultStyle) = Empty()

function (lwr::AsymptoticAnalysis)(root::Assign, ::DefaultStyle)
    return Times(lwr.qnts...)
end

function (lwr::AsymptoticAnalysis)(stmt::Loop, ::DefaultStyle)
    quantify(lwr, stmt.idxs...)(stmt.body)
end

struct CoiterateStyle
    style
    verified
end

make_style(lwr::AsymptoticAnalysis, root::Loop, node::HollowSymbolicTensor) = CoiterateStyle(DefaultStyle(), false)
resolve_style(lwr::AsymptoticAnalysis, root::Loop, node::Access, style::CoiterateStyle) =
    ((!isempty(root.idxs) && root.idxs[1] in node.idxs) || style.verified) ? CoiterateStyle(style.style, true) :
        resolve_style(lwr, root, node, style.style)
combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle(result_style(a.style, b.style), a.verified | b.verified)

#TODO generalize the interface to annihilation analysis
annihilate_index = Fixpoint(Postwalk(Chain([
    (@expand@rule i"~f(~~a)" => if isliteral(~f) && all(isliteral, ~~a) Literal(value(~f)(value.(~~a)...)) end),
    (@expand@rule i"+(~~a, +(~~b), ~~c)" => i"+(~~a, ~~b, ~~c)"),
    (@expand@rule i"+(~~a)" => if any(isliteral, ~~a) i"+($(filter(!isliteral, ~~a)), $(Literal(+(value.(filter(isliteral, ~~a))...))))" end),
    (@expand@rule i"+(~~a, 0, ~~b)" => i"+(~~a, ~~b)"),

    (@expand@rule i"*(~~a, *(~~b), ~~c)" => i"*(~~a, ~~b, ~~c)"),
    (@expand@rule i"*(~~a)" => if any(isliteral, ~~a) i"*($(filter(!isliteral, ~~a)), $(Literal(*(value.(filter(isliteral, ~~a))...))))" end),
    (@expand@rule i"*(~~a, 1, ~~b)" => i"*(~~a, ~~b)"),
    (@expand@rule i"*(~~a, 0, ~~b)" => Literal(0)),

    (@expand@rule i"+(~a)" => ~a),
    (@expand@rule i"~a - ~b" => i"~a + (- ~b)"),
    (@expand@rule i"- (- ~a)" => ~a),
    (@expand@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
    (@expand@rule i"*(~a)" => ~a),
    (@expand@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),

    #(@expand@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
    #(@expand@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)

    (@expand@rule i"~a[~~i] = 0" => Pass()), #TODO this is only valid when the default of A is 0
    (@expand@rule i"~a[~~i] += $(Literal(0))" => Pass()),
])))

function (lwr::AsymptoticAnalysis)(stmt::Loop, ::CoiterateStyle)
    lwr′ = quantify(lwr, stmt.idxs[1])
    Cup(coiterate_asymptote(lwr′, stmt),
        mapreduce(Cup, coiterate_cases(lwr′, Loop(stmt.idxs[2:end], stmt.body))) do (guard, body)
            Such(lwr′(annihilate_index(body)), guard)
        end)
end

coiterate_asymptote(lwr, node) = _coiterate_asymptote(lwr, node)
function _coiterate_asymptote(lwr, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote(lwr, arg), Cup, arguments(node))
    else
        return false
    end
end
coiterate_asymptote(lwr, root, stmt::Access) = coiterate_asymptote(lwr, root, stmt::Access, stmt.tns)
coiterate_asymptote(lwr, root, stmt::Access, tns) = _coiterate_asymptote(lwr, root)
function coiterate_asymptote(lwr, root, stmt::Access, tns::HollowSymbolicTensor)
    root.idxs[1] in stmt.idxs[1] || return Empty()
    return Such(Times(lwr.qnts...), Exists(name.(filter(j->!(j ∈ lwr.qnts), stmt.idxs))...,
                Predicate(name.(arguments(stmt))...)))
end

coiterate_cases(lwr, node) = _coiterate_cases(lwr, node)
function _coiterate_cases(lwr, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(lwr, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(true, node),]
    end
end
coiterate_cases(lwr, stmt::Access) = coiterate_cases(lwr, stmt::Access, stmt.tns)
coiterate_cases(lwr, stmt::Access, tns) = _coiterate_cases(lwr, stmt)
function coiterate_cases(lwr, stmt::Access, tns::HollowSymbolicTensor)
    if !isempty(stmt.idxs) && stmt.idxs[1] in lwr.qnts
        return [(Exists(name.(filter(j->!(j ∈ lwr.qnts), stmt.idxs))...,
                Predicate(name.(arguments(stmt))...)), stmt),
            (true, Literal(0)),]
    else
        return [(true, stmt),]
    end
end