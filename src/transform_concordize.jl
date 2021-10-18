concordize(node) = concordize(node, [])

function concordize(node::Loop, qnts)
    return Loop(node.idxs, concordize(node.body, vcat(qnts, node.idxs)))
end

function concordize(node, qnts)
    if istree(node)
        return similarterm(node, operation(node), map(arg->concordize(arg, qnts), arguments(node)))
    else
        return node
    end
end

function concordize(node::Access, qnts)
    σ = sortperm(node.idxs, by = idx->findlast(isequal(idx), qnts), alg=Base.DEFAULT_STABLE)
    (tns, σ) = retranspose(node.tns, σ)
    return Access(tns, node.mode, node.idxs[σ])
end

function retranspose(tns::SymbolicHollowTensor, σ)
    tns = copy(tns)
    tns.perm = tns.perm[σ]
    tns.format = tns.format[σ]
    tns.dims = tns.dims[σ]
    return (tns, σ)
end

function retranspose(tns::SymbolicSolidTensor, σ)
    tns = copy(tns)
    tns.perm = tns.perm[σ]
    tns.dims = tns.dims[σ]
    return (tns, σ)
end