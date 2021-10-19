struct ReformContext
end

function reform(acc::Access{SymbolicHollowTensor, Update}, ctx)
    qnts = ctx.qnts[ctx.nest(getname(acc.tns)) : end] #only want qnts since tensor was initialized

    l_ins = findfirst(l->qnts[l] != acc.idx[l], 1 : length(acc.idx))

    if l_ins != nothing
        name′ = freshen(getname(tns))
        idxs′ = intersect(qnts[l_ins : end], acc.idxs)
        tns′ = SymbolicHollowTensor(
            name,
            [locate for _ in idxs′],
            [dims[]]
            tns.default
            collect(1:length(idxs′))
            tns.implicit
        )
        acc′ = intersect(qnts[l_ins : end], acc.idxs)[tns.prm]
        acc′ = Accintersect(qnts[l_ins : end], acc.idxs)[tns.prm]

        push!(ctx.sites[l_ins], @i @loop acc′_idxs acc[acc.idxs[tns.prm]] += acc)
        push!(ctx.sites[l_ins], @i @loop acc′_idxs acc[acc.idxs[tns.prm]] += acc)
        Loop(acc.idxs[tns.perm], Access)
    end
end

#Do a pass with insert < Check if outputs need reformat or permute
#Do a pass with permute < Check if outputs need reformat
#Do a pass with reformat

function adapt!(prg, qnt)
    qnt
end

if previous indices are quantified, mark current index as described
while there are still quantified indices, mark each index as locate

#High level: this pass is going to tell us how indices are really accessed
#

isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
isempty(root.idxs) && return DefaultStyle()
i = findfirst(isequal(root.idxs[1]), node.idxs)
(i !== nothing && node.idxs[1:i - 1] ⊆ ctx.qnts) || return DefaultStyle()
node.tns.format[i] === coiter || return DefaultStyle()
return CoiterateStyle()

#assume concordized to make life easier.

#An insert is a "scatter" if there is a quantified index before an access index that does not
#support scatter.
#all indices that occur after the quantified index need a workspace.

#A write is out of order if the indices are permuted.
#All indices that occur after the first out of order index need a workspace.

#A read is out of order if the indices are permuted.
#All indices that occur after the first out of order index need a workspace.

#Question: Do we apply this transformation to workspaces or just input/output?

#Observation: This transformation applies to tensors at their "initialization point"

#Options are either:
#Keep a list of inputs and their names
#Wrap inputs in some sort of "adaptor" type
#Pros:
#   Won't work if there are multiple inputs
#   Convenience of having wrapped tensor available isn't useful in the read case, we already need to cross-reference tensor identity

function reform(acc::Access{SymbolicHollowTensor, Update}, ctx)
    qnts = ctx.qnts[ctx.nest(getname(acc.tns)) : end] #qnts is only qnts since tensor was initialized

    l_prm = findfirst(l->tns.perm[l] != l, 1 : length(tns.prm))
    l_ins = findfirst(l->qnts[l] != acc.idx[l], 1 : length(acc.idx))

    if l_prm != nothing
        push a permutation
    end
    if l_ins != nothing
        acc′_idxs = intersect(qnts[l_ins : end], acc.idxs)[tns.prm]
        push!(ctx.sites[l_ins], @i @loop acc′_idxs acc[acc.idxs[tns.prm]] += acc)
        Loop(acc.idxs[tns.perm], Access[])
    end
    if l_prm < l_ins
        acc′_idxs = intersect(qnts[l_prm:end], acc.idxs)
    end
end

struct ReformContext
    qnts
    binds
end

ReformContext() = ReformContext([], [[]])

function reform(root)
    ctx = ReformContext()
    res = reform(root, ctx)
    for bind in binds
        res = With(res, bind)
    end
    return res
end

#root scope might be more critical than I thought

function reform(root::Loop, ctx)
    isempty(root.idxs) && return reform(root.body, ctx)
    push!(ctx.qnts, idx)
    push!(ctx.binds, [])
    res = Loop(root.idx[1], reform(Loop(root.idxs[2:end], root.body)))
    binds = pop!(ctx.binds)
    pop!(ctx.qnts)
    for bind in binds
        res = With(res, bind)
    end
    return res
end

function reform(root::With, qnt)
    prod_cpys = reform(root.prod)
    cons_cpys = reform(root.cons)
    result(root.prod) = reform(root.cons)
end

function reform_loop(root, qnt)
    if reform_loop(root.idx)

    end
end
