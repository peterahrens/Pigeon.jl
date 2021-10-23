mutable struct ReformatContext
    nest
    qnt
    qnt′
end

transform_reformat(node) = transform_reformat(node, ReformatContext(Dict(), [], []))

transform_reformat(node, ctx) = transform_reformat(node, ctx, make_style(node, ctx))

function make_style(root, ctx::ReformatContext, node::Loop)
    append!(ctx.qnt′, node.idxs)
    style = resolve_style(root, ctx, node, make_style(root, ctx, node.body))
    for idx in node.idxs pop!(ctx.qnt′) end
    return style
end

function make_style(root, ctx::ReformatContext, node::With)
    prod_style = transform_reformat_collect(node.prod, ctx)
    ctx.nest[name(getresult(node.prod))] = length(ctx.qnt′)
    cons_style = transform_reformat_collect(node.cons, ctx)
    delete!(ctx.nest, name(getresult(node.prod)))
    return resolve_style(root, ctx, node, result_style(prod_style, cons_style))
end

function transform_reformat(node::Loop, ctx, ::DefaultStyle)
    isempty(node.idxs) && return transform_reformat(node.body, ctx)
    push!(ctx.qnt, node.idxs[1])
    push!(ctx.qnt′, node.idxs[1])
    body′ = transform_reformat(Loop(node.idxs[2:end], node.body), ctx)
    pop!(ctx.qnt)
    pop!(ctx.qnt′)
    return Loop(Any[node.idxs[1]], body′)
end

function transform_reformat(node::With, ctx, ::DefaultStyle)
    prod = transform_reformat(node.prod, ctx)
    ctx.nest[getresult(node.prod)] = length(ctx.qnts)
    prod = transform_reformat(node.cons, ctx)
    delete!(getresult(node.prod))
end

function transform_reformat(node, ctx, ::DefaultStyle)
    if istree(node)
        similarterm(node, operation(node), map(arg -> transform_reformat(arg, ctx), arguments(node)))
    else
        node
    end
end



struct ReformatTempStyle
    tns
    keep
    idxs
    protocols
end

function make_style(root, ctx::ReformatContext, node::Access{SymbolicHollowDirector})
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        #push a tensor reformat as far down the nest as we can, without computing it redundantly
        keep = findfirst(i->ctx.qnt′[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
        if keep == 1 && haskey(ctx.nest, getname(node.tns))
            if root isa With && getname(getresult(root.prod)) == getname(node.tns)
                return ReformatWithStyle(node.tns.tns, format, protocol)
            end
        elseif top + keep == length(ctx.qnt)
            return ReformatTempStyle(node.tns.tns, keep, node.idxs[1:keep-1], Set([protocol]))
        end
    end
    return DefaultStyle()
end

function combine_style(a::ReformatTempStyle, b::ReformatTempStyle)
    if a.tns == b.tns
        return ReformatTempStyle(a.tns, min(a.keep, b.keep), intersect(a.idxs, b.idxs), union(a.protocols, b.protocols))
    end
    return getname(a.tns) < getname(b.tns) ? a : b
end

function transform_reformat(root, ctx::ReformatContext, style::ReformatTempStyle)
    protocols = unzip(style.protocols)
    format′ = [foldl(widenformat, protocols[i], init = NoFormat()) for i = style.keep:length(getformat(style.tns))]
    println((format′, style.tns.format))
    name′ = freshen(getname(style.tns))
    dims′ = style.tns.dims[style.keep:end]
    tns′ = SymbolicHollowTensor(name′, format′, dims′, style.tns.default)
    idxs′ = [Name(gensym()) for _ in format′]
    #for now, assume that a different pass will add "default" read/write protocols
    prod′ = @i (@loop $idxs′ $tns′[$idxs′] = $(style.tns)[$(style.idxs), $idxs′])
    substitute_reformat(node) = node
    function substitute_reformat(node::Access{SymbolicHollowDirector})
        if style.tns == node.tns.tns
            if !all(i -> hasprotocol(getformat(node.tns)[i], getprotocol(node.tns)[i]), 1:length(getformat(node.tns)))
                return Access(SymbolicHollowDirector(tns′, getprotocol(node.tns)[style.keep:end]), node.mode, node.idxs[style.keep:end])
            end
        end
        node
    end
    cons′ = Postwalk(substitute_reformat)(root)
    return With(transform_reformat(cons′), prod′)
end

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



#=
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
=#