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

struct Namespace
    renames
    binds
end

Namespace() = Namespace(Dict(), [])

function resolvename!(root, ctx::Namespace)
    name = getname(root)
    if haskey(ctx.renames, name)
        if isempty(ctx.renames[name]) #redefining global name
            name′ = freshen(name)
            push!(ctx.renames[name], name′)
            return rename(root, name′)
        else
            return rename(root, ctx.renames[name][end])
        end
    else
        ctx.renames[name] = Any[name]
        return rename(root, name)
    end
end

function definename!(root, ctx::Namespace)
    name = getname(root)
    push!(ctx.binds, name)
    if haskey(ctx.renames, name)
        name′ = freshen(name)
        push!(ctx.renames[name], name′)
        return rename(root, name′)
    else
        ctx.renames[name] = Any[name]
        return rename(root, name)
    end
end

function scope(f::F, ctx::Namespace) where {F}
    binds′ = []
    res = f(Namespace(ctx.renames, binds′))
    for name in binds′
        pop!(ctx.renames[name])
    end
    return res
end

function transform_ssa(prgm)
    transform_ssa!(prgm, Namespace())
end

function transform_ssa!(root::Name, ctx)
    resolvename!(root, ctx)
end

function transform_ssa!(root::Loop, ctx)
    scope(ctx) do ctx′
        idxs = map(idx->definename!(idx, ctx′), root.idxs)
        body = transform_ssa!(root.body, ctx)
        return loop(idxs, body)
    end
end

function transform_ssa!(root::With, ctx)
    scope(ctx) do ctx′
        prod = transform_ssa!(root.prod, ctx′)
        cons = transform_ssa!(root.cons, ctx)
        return with(cons, prod)
    end
end

transform_ssa!(root, ctx) = _transform_ssa!(root, ctx)
function _transform_ssa!(root, ctx)
    if istree(root)
        return similarterm(root, operation(root), map(arg->transform_ssa!(arg, ctx), arguments(root)))
    else
        return root
    end
end

function transform_ssa!(root::Access, ctx)
    if root.mode != Read()
        tns = definename!(root.tns, ctx)
    else
        tns = resolvename!(root.tns, ctx)
    end
    return Access(tns, root.mode, map(idx->transform_ssa!(idx, ctx), root.idxs))
end