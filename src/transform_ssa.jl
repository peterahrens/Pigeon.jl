struct Freshie
    name
    n::Int
end

function Base.show(io::IO, ex::Freshie)
    print(io, ex.name)
    print(io, "_")
    print(io, ex.n)
end

fresh_num = 0

freshen(ex::Symbol) = Freshie(ex, global fresh_num += 1)
freshen(ex::Freshie) = Freshie(ex.name, global fresh_num += 1)

function transform_ssa(prgm)
    renames = Dict()
    transform_ssa!(prgm, renames)
end

poprename!(renames, name) = pop!(renames[name])

function pushrename!(renames, name)
    if haskey(renames, name)
        push!(renames[name], freshen(name))
    else
        renames[name] = Any[name]
        name
    end
end

function getrename!(renames, name)
    if haskey(renames, name) && !isempty(renames[name])
        return renames[name][end]
    else
        renames[name] = Any[name]
        name
    end
end
        
function transform_ssa!(root::Loop, renames)
    for idx in root.idxs
        pushrename!(renames, getname(idx))
    end
    res = _transform_ssa!(root, renames)
    for idx in root.idxs
        poprename!(renames, getname(idx))
    end
    return res
end

function transform_ssa!(root::With, renames)
    cons = transform_ssa!(root.cons, renames)
    prod = transform_ssa!(root.prod, renames)
    poprename!(renames, getname(getresult(root.prod)))
    return With(cons, prod)
end

transform_ssa!(root::IndexNode, renames) = _transform_ssa!(root, renames)
function _transform_ssa!(root::IndexNode, renames)
    if istree(root)
        return similarterm(root, operation(root), map(arg->transform_ssa!(arg, renames), arguments(root)))
    else
        return root
    end
end

function transform_ssa!(root::Assign, renames)
    lhs = transform_ssa!(root.lhs, renames)
    pushrename!(renames, getname(getresult(root.lhs)))
    op = root.op === nothing ? root.op : transform_ssa!(root.op, renames)
    rhs = transform_ssa!(root.rhs, renames)
    return Assign(lhs, op, rhs)
end

function transform_ssa!(root::Name, renames)
    Name(getrename!(renames, getname(root)))
end

function transform_ssa!(root, renames)
    rename(root, getrename!(renames, getname(root)))
end

function rename end