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

struct ReformatContext
    needed
end

function transform_reformat(root)
    ctx = ReformatContext(Dict())
    Postwalk(node->transform_reformat_collect(node, ctx))(root)
    return ctx.needed
end

transform_reformat_collect(node, ctx) = nothing
function transform_reformat_collect(node::Access{SymbolicHollowTensor}, ctx)
    name = getname(node.tns)
    format = getformat(node.tns)
    props = get!(ctx.needed, name, [Set() for _ in format])
    for (i, mode) in enumerate(format)
        push!(props[i], accessstyle(mode))
    end
end

accessstyle(mode) = mode #needs fixing