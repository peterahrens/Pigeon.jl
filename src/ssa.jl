function ssa_index(prgm)
    names = Dict()
    Prewalk(node->ssa_index!(names, node))(prgm)
end

function ssa_index!(root::Loop, names)
    for idx in root.idxs
        haskey(names, idx) ? push!(names[idx], freshen(idx)) : names[idx] = [idx]
    end
    body = ssa_index!(root.body, names)
    idxs = map(idx->names[idx], root.idxs)
    for idx in root.idxs
        pop!(names[idx])
    end
    return Loop(idxs, body)
end

function ssa_index!(root::With, names)
    prod = ssa_index!(root.prod, names)
    cons = ssa_index!(root.cons, names)
    pop!(names[producer])
    return With(prod, cons)
end

ssa_index!(root, names) = _ssa_index!(root, names)
function _ssa_index!(root::IndexNode, names)
    if istree(root)
        return similarterm(root, operation(root), map(arg->ssa_index!(arg, names), arguments(root)))
    else
        return root
    end
end

function ssa_index!(root::Assign, names)
    tns = name(producer(root))
    haskey(names, tns) ? push!(names[tns], freshen(tns)) : names[idx] = [idx]
    _ssa_index(root, names)
end

function ssa_index!(root::Name, names)
    get!(names, root, [name(root)])
end