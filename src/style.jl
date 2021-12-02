struct DefaultStyle end
struct UnknownStyle end

visit!(node, ctx) = visit!(node, ctx, make_style(node, ctx))

make_style(root, ctx) = make_style(root, ctx, root)
function make_style(root, ctx, node)
    if istree(node)
        #m = map(arg->make_style(root, ctx, arg), arguments(node))
        #r = reduce(result_style, m)
        #s = resolve_style(root, ctx, node, r)
        #@info "hmm" m r s node
        return resolve_style(root, ctx, node, mapreduce(arg->make_style(root, ctx, arg), result_style, arguments(node)))
        #return s
    end
    return DefaultStyle()
end

result_style(a, b) = _result_style(combine_style(a, b), combine_style(b, a))
_result_style(a::UnknownStyle, b::UnknownStyle) = throw(MethodError(combine_style, a, b))
_result_style(a, b::UnknownStyle) = a
_result_style(a::UnknownStyle, b) = b
_result_style(a::T, b::T) where {T} = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
_result_style(a, b) = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
combine_style(a, b) = UnknownStyle()

combine_style(a::DefaultStyle, b) = b
resolve_style(root, ctx, node, style) = style

abstract type AbstractTraverseContext end

function visit!(node, ctx::AbstractTraverseContext, style::DefaultStyle)
    node = previsit!(node, ctx)
    if istree(node)
        postvisit!(node, ctx, map(arg->visit!(arg, ctx), arguments(node)))
    else
        postvisit!(node, ctx)
    end
end

abstract type AbstractTransformContext <: AbstractTraverseContext end

previsit!(node, ctx::AbstractTransformContext) = node
postvisit!(node, ctx::AbstractTransformContext, args) = similarterm(node, operation(node), args)
postvisit!(node, ctx::AbstractTransformContext) = node

abstract type AbstractCollectContext <: AbstractTraverseContext end
function collector end

previsit!(node, ctx::AbstractCollectContext) = node
postvisit!(node, ctx::AbstractCollectContext, args) = collector(ctx)(args)
postvisit!(node, ctx::AbstractCollectContext) = node #TODO an arguably bad default.

abstract type AbstractWalkContext <: AbstractTraverseContext end

previsit!(node, ctx::AbstractWalkContext) = node
postvisit!(node, ctx::AbstractWalkContext, args) = nothing
postvisit!(node, ctx::AbstractWalkContext) = nothing



abstract type AbstractWrapperContext <: AbstractTraverseContext end

previsit!(node, ctx::AbstractWrapperContext) = previsit!(node, getparent(ctx))
postvisit!(node, ctx::AbstractWrapperContext, args) = transform(node, getparent(ctx), args)
postvisit!(node, ctx::AbstractWrapperContext) = postvisit!(node, getparent(ctx))

getdata(ctx) = ctx
getdata(ctx::AbstractWrapperContext) = getdata(getparent(ctx))



Base.@kwdef struct QuantifiedContext{Ctx} <: AbstractTraverseContext
    parent::Ctx
    qnt = []
    diff = []
end

getparent(ctx::QuantifiedContext) = ctx.ctx
getqnt(ctx::QuantifiedContext) = ctx.qnt
getqnt(ctx) = getqnt(getparent(ctx))

function previsit!(node, ctx::QuantifiedContext)
    push!(diff, 0)
end
function previsit!(node::Loop, ctx::QuantifiedContext)
    append!(ctx.qnt, node.idxs)
    push!(diff, length(node.idxs))
    previsit!(node, ctx.ctx)
end
function postvisit!(node, ctx::QuantifiedContext)
    for i in 1:pop!(node.diff)
        pop!(ctx.qnt)
    end
end