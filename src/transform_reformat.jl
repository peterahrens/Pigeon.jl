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
    trns
    nest
    qnt
end

struct ReformatTransform
    tns
    idxs
    qnt
    protos
end

function transform_reformat_merge(a::ReformatTransform, b::ReformatTransform)
    a.tns == b.tns || return nothing
    a.idxs == b.idxs || return nothing
    l = min(length(a.qnt), length(b.qnt))
    a.qnt[1:l] == b.qnt[1:l] || return nothing
    return ReformatTransform(a.name, a.idxs, a.qnt[1:l], vcat(a.protos, b.protos))
end

#assumes concordant, ssa, and a single permutation for each tensor
function transform_reformat(root)
    ctx = ReformatContext([], Dict(), [])
    transform_reformat_collect(root, ctx)

    trns = []
    for a in ctx.trns
        trns′ = []
        for b in trns
            a′ = transform_reformat_merge(a, b)
            if a′ !== nothing
                a = a′
            else
                push!(trns′, b)
            end
        end
        push!(trns′, a)
        trns = trns′
    end

    return trns
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

function transform_reformat_collect(node::Access{SymbolicHollowDirector}, ctx)
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        #push a tensor reformat as far down the nest as we can, without computing it redundantly
        i = findfirst(i->ctx.qnt[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
        
        res = ReformatTransform(name, node.idxs, top == 0, ctx.qnt[top + 1 : top + i], protocol)
        push!(ctx.trns, res)
    end
end

#=
function transform_reformat_execute(node::Loop, ctx)
    isempty(node.idxs) && return transform_reformat_collect(node.body)
    push!(ctx.qnt, node.idxs[1])
    #!isempty(trn.qnt) && subseteq(trn.qnt, ctx.qnt)
    transform_reformat_collect(Loop(node.idxs[2:end], node.body), ctx)
    pop!(ctx.qnt)
end

function transform_reformat_execute(node::With, ctx)
    transform_reformat_execute(node.prod, ctx)
    res = getresult(node.prod)
    ctx.nest[res] = length(ctx.qnts)
    #isempty(trn.qnt) && getname(trn.tns) == getname(res)
    transform_reformat_execute(node.cons, ctx)
    delete!(res)
end

function transform_reformat_execute(node, ctx)
    if istree(node)
        similarterm(node, map(arg -> transform_reformat_execute(arg, ctx), arguments(node)))
    else
        node
    end
end

function transform_reformat_execute(node::Access{SymbolicHollowDirector}, ctx)
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        
    end
end
=#