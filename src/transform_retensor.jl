#walk the program and replace all the tensors with the replacer function
#assumes unique identities (ssa)

struct ReplacerContext{F}
    tnss
    replacer::F
end
function transform_retensor(node, ctx)
    if istree(node)
        similarterm(node, map(arg->transform_retensor(arg, ctx), arguments(node)))
    else
        node
    end
end
transform_retensor_substitute(node::Access, ctx) = transform_retensor(node, ctx)
transform_retensor(node::Access, ctx)
    return Access(transform_retensor_substitute(node.tns, ctx), node.mode, node.idxs)
end
transform_retensor(node::Pass, ctx)
    return Pass(transform_retensor_substitute(node.tns, ctx))
end
function transform_retensor_substitute(node, ctx)
    push!(ctx.tnss, node)
    return ctx.replacer(node)
end