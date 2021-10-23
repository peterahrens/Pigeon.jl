mutable struct ReformatContext
    nest
    qnt
    qnt′
    style
end

transform_reformat(node) = transform_reformat(node, ReformatContext(Dict(), [], [], nothing))

function transform_reformat(node, ctx)
    ctx.style = make_style(node, ctx)
    style = make_style(node, ctx)
    ctx.style = nothing
    transform_reformat(node, ctx, style)
end

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



struct ReformatReadStyle
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
    style = DefaultStyle()
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        #push a tensor reformat as far down the nest as we can, without computing it redundantly
        keep = findfirst(i->ctx.qnt′[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
        if keep == 1 && haskey(ctx.nest, getname(node.tns))
            if root isa With && getname(getresult(root.prod)) == getname(node.tns)
                style = ReformatWithStyle(node.tns.tns, format, protocol)
            end
        elseif top + keep == length(ctx.qnt)
            style = ReformatReadStyle(node.tns.tns, keep, node.idxs[1:keep-1], Set([protocol]))
        end
    end
    return isapplicable(ctx.style, style) ? style : DefaultStyle()
end

isapplicable(::Nothing, style) = true
isapplicable(root_style::ReformatReadStyle, style::ReformatReadStyle) = root_style.tns == style.tns
isapplicable(::DefaultStyle, ::ReformatReadStyle) = false
isapplicable(::ReformatReadStyle, ::DefaultStyle) = true
isapplicable(::DefaultStyle, ::DefaultStyle) = true

function combine_style(a::ReformatReadStyle, b::ReformatReadStyle)
    if a.tns == b.tns
        return ReformatReadStyle(a.tns, min(a.keep, b.keep), intersect(a.idxs, b.idxs), union(a.protocols, b.protocols))
    end
    return getname(a.tns) < getname(b.tns) ? a : b
end

function transform_reformat(root, ctx::ReformatContext, style::ReformatReadStyle)
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