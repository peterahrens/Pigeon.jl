quantify(ctx::AsymptoticContext, vars...) = AsymptoticContext(union(ctx.qnts, vars))

abstract type TransformContext end

lower(root) = lower(root, AsymptoticContext())[1]

merge_context(ctx, ctx′) = UnimplementedError()


"""
    lowerers return a three tuple (resolution, result, new_ctx)
"""
lower(root, ctx)

lower(root::Literal, ctx::TransformContext) = (root, nothing, ctx)
lower(root::Name, ctx::TransformContext) = (root, nothing, ctx)

lower(root::Access, ctx) = lower_access(root.tns, root.idxs, ctx)
function lower_access(tns, idxs, ctx::TransformContext)
    (idxs, ctx) = mapfoldl(idx->lower(idx, ctx), merge_context, idxs)
    return lower(tns)
end
function lower(root::Assign, ctx)
    @assert root.lhs isa Access
    lower_assign(root.tns, root.idxs, root.op, root.rhs, ctx)
end
lower_assign(root.tns, root.idxs, root.op, root.rhs, ctx)

function lower(root::Where, ctx)
    (prod_res, ctx) = lower(root.prod, ctx)
    (cons_res, ctx) = lower(root.cons, ctx)
end



lower(root::Pass, ctx::TransformContext) = (root, nothing, ctx)


mapfoldl
asymptote_merge

asymptote(root::Assign, ctx) = asymptote_assign(root.lhs, (root.op === nothing ? Empty() : asymptote(root.op, ctx), asymptote(root.rhs, ctx), idxs)
asymptote_assign(root::Access, op, rhs, ctx) = asymptote_assign_access(root.tns, map(idx->asymptote(idx, ctx), root.idxs), op, rhs, ctx)
asymptote_assign_access(root, idxs, op, rhs, ctx) = (Times(name.(ctx.qnts)...), Dict(name(root)=>ctx.guard)
asymptote_where

lower_assign_access(, op, rhs)