mutable struct PointQuery
    points
end

struct SymbolicFiberArray
    name
    format
    default
    implicit #describes whether this tensor initially holds entirely implicit values
    data
end

postwalk()



    if !isempty(stmt.idxs) && root.idxs[1] in stmt.idxs
        return [(coiterate_predicate(ctx, tns, stmt.idxs), stmt),
            (ctx.guard, tns.default),]
    else
        return [(ctx.guard, stmt),]
    end


coiterate_asymptote(root, ctx, stmt::Access) = coiterate_asymptote(root, ctx, stmt, stmt.tns)
coiterate_asymptote(root, ctx, stmt, tns) = _coiterate_asymptote(root, ctx, stmt)
function coiterate_asymptote(root, ctx, stmt, tns::SymbolicCoiterableTensor)
    root.idxs[1] in stmt.idxs || return
    iterate!(ctx, coiterate_predicate(ctx, tns, stmt.idxs))
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
    stmt′ = Assign(_coiterate_processed(stmt.lhs, coiterate_predicate(ctx, tns, stmt.lhs.idxs)), stmt.op, stmt.rhs)
    if !isempty(stmt.lhs.idxs) && root.idxs[1] in stmt.lhs.idxs
        stmt′′ = Assign(_coiterate_processed(Access(implicit(tns), stmt.lhs.idxs)), stmt.op, stmt.rhs)
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