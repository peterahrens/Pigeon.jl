#this game is different depending on whether a tensor is carry-in, carry-out, or workspace

#gameplan: walk the expression, and see what properties the consumers need.

#assume concordized for simplicity

#Then, check
#that the producers are providing it. If the tensor is a global, then "What the producers need"
#is just whatever the output format is. Easiest to assume ssa here, but you do you ;)

#This pass is interesting because it just "widens" input formats

#Simplest approach is to just walk the whole expr, assume ssa, and check what format everything needs. Emit the index of the loop where the property is needed?
#Figure out everything else later.

#check if there is a tensor at or before your insertion location to see if we can widen that format instead.

#assuming each tensor has one source is safe because we can try every combination of sources.

struct ReformatContext
    ops
    nest
    qnt
end

struct ReformatOperation
    name
    idxs
    qnts
    protocols
end

#assumes concordant, ssa, and a single permutation for each tensor
function transform_reformat(root)
    ctx = ReformatContext([], Dict(), [])
    transform_reformat_collect(root, ctx)
    return ctx.needed
end

function transform_reformat_collect(node::Loop, ctx)
    append!(ctx.qnt, node.idxs)
    transform_reformat_collect(node.body, ctx)
    for idx in node.idxs pop!(ctx.qnt) end
end

function transform_reformat_collect(node::With, ctx)
    transform_reformat_collect(node.prod, ctx)
    ctx.nest[getresult(node.prod)] = length(ctx.qnts)
    transform_reformat_collect(node.cons, ctx)
    delete!(getresult(node.prod))
end

function transform_reformat_collect(node, ctx)
    if istree(node)
        map(arg -> transform_reformat_collect(arg, ctx), arguments(node))
    else
        nothing
    end
end

function transform_reformat_collect(node::Access{<:AbstractSymbolicHollowTensor}, ctx)
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    #push a tensor reformat as far down the nest as we can, without computing it redundantly
    i = findfirst(i->ctx.qnt[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
    res = ReformatOperation(name, node.idxs, ctx.qnt[top + 1: top + i], protocol)
    println(res)
end

accessstyle(mode) = mode #needs fixing