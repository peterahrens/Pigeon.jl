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

mutable struct ReformatContext
    trns
    nest
    qnt
    tnss
end

struct ReformatRequest
    tns
    keep
    qnt
    protos
end

function transform_reformat_merge(a::ReformatRequest, b::ReformatRequest)
    a.tns == b.tns || return nothing
    l = min(length(a.qnt), length(b.qnt))
    a.qnt[1:l] == b.qnt[1:l] || return nothing
    return ReformatRequest(a.tns, min(a.keep, b.keep), a.qnt[1:l], vcat(a.protos, b.protos))
end

function transform_reformat_process(trn::ReformatRequest)
    protocol_groups = unzip(trn.protos)
    format = getformat(trn.tns)
    i = findfirst(i -> i >= trn.keep && !all(proto -> hasprotocol(format[i], proto), protocol_groups[i]), 1:length(format))
    format′ = map(j -> foldl(widenformat, protocol_groups[j], init=NoFormat()), i:length(format))
    name′ = freshen(trn.tns.name)
    dims′ = trn.tns.dims[i:length(format)]
    tns′ = SymbolicHollowTensor(name′, format′, dims′, trn.tns.default)
    idxs′ = [Name(gensym()) for _ in format′]
    #for now, assume that a different pass will add "default" read/write protocols
    prod′ = @i @loop $idxs′ $tns′[$idxs′] = $(trn.tns)[$(trn.qnt), $idxs′]
    return ReformatResponse(trn.tns.name, tns′, prod′, trn.keep, trn.qnt)
end

struct ReformatResponse
    name
    tns
    prod
    keep
    qnt
end

#assumes concordant, ssa, and a single permutation for each tensor
function transform_reformat(root)
    ctx = ReformatContext([], Dict(), [], Dict())
    for name in getglobals(root)
        ctx.nest[name] = 0
    end
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

    trns = map(transform_reformat_process, trns)
    ctx.trns = trns

    return transform_reformat_execute(root, ctx)
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
        i = findfirst(i->ctx.qnt[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format)) - 1

        res = ReformatRequest(node.tns.tns, i, ctx.qnt[1 : top + i], [protocol])
        push!(ctx.trns, res)
    end
end

function transform_reformat_execute(node::Loop, ctx)
    isempty(node.idxs) && return transform_reformat_execute(node.body, ctx)
    push!(ctx.qnt, node.idxs[1])
    prods = []
    tns = []
    trns′ = []
    names = []
    for trn in ctx.trns
        if !isempty(trn.qnt) && issubset(trn.qnt, ctx.qnt)
            push!(prods, trn.prod)
            ctx.tnss[trn.name] = trn.tns
            push!(names, trn.name)
        else
            push!(trns′, trn)
        end
    end
    ctx.trns = trns′
    body′ = transform_reformat_execute(Loop(node.idxs[2:end], node.body), ctx)
    pop!(ctx.qnt)
    for name in names
        delete!(ctx.tnss, name)
    end
    return Loop(Any[node.idxs[1]], foldl(with, prods, init=body′))
end

function transform_reformat_execute(node::With, ctx)
    transform_reformat_execute(node.prod, ctx)
    res = getresult(node.prod)
    ctx.nest[res] = length(ctx.qnts)
    #isempty(trn.i) && getname(trn.tns) == getname(res)
    transform_reformat_execute(node.cons, ctx)
    delete!(res)
end

function transform_reformat_execute(node, ctx)
    if istree(node)
        similarterm(node, operation(node), map(arg -> transform_reformat_execute(arg, ctx), arguments(node)))
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
        if haskey(ctx.tnss, name)
            tns = ctx.tnss[name]
            tns = SymbolicHollowDirector(tns, node.tns.protocol[end - length(tns.format) + 1: end])
            return Access(tns, node.mode, node.idxs[end - length(tns.protocol) + 1: end])
        end
    end
    return node
end