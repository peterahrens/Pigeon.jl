mutable struct ReformatContext
    nest
    qnt
    qnt′
end

transform_reformat(node) = transform_reformat(node, ReformatContext(Dict(), [], []))

function transform_reformat(node, ctx)
    tasks = transform_reformat_collect(node, ctx, node)
    
    #merge tasks into a sorted list of actions
    acts = []
    for task in tasks
        acts′ = []
        for act in acts
            res = result_task(act, task) 
            if res !== nothing
                task = res
            else
                push!(acts′, act)
            end
        end
        push!(acts′, task)
        acts = acts′
    end

    #choose an action to perform

    transform_reformat(node, ctx, foldl(choose_task, acts, init = DefaultTask()))
end

function transform_reformat_collect(root, ctx, node)
    if istree(node)
        return mapreduce(arg->transform_reformat_collect(root, ctx, arg), vcat, arguments(node))
    end
    return [DefaultTask()]
end

function transform_reformat_collect(root, ctx::ReformatContext, node::Loop)
    append!(ctx.qnt′, node.idxs)
    res = transform_reformat_collect(root, ctx, node.body)
    for idx in node.idxs pop!(ctx.qnt′) end
    return res
end

function transform_reformat_collect(root, ctx::ReformatContext, node::With)
    prod_tasks = transform_reformat_collect(node.prod, ctx)
    ctx.nest[name(getresult(node.prod))] = length(ctx.qnt′)
    cons_tasks = transform_reformat_collect(node.cons, ctx)
    delete!(ctx.nest, name(getresult(node.prod)))
    return vcat(prod_tasks, cons_tasks)
end

struct UnknownTask end
struct DefaultTask end
struct PriorityTask
    task
end
result_task(a, b) = __result_task(_result_task(combine_task(a, b), combine_task(b, a)))
__result_task(::PriorityTask) = nothing
__result_task(task) = task
choose_task(a, b) = _choose_task(_result_task(combine_task(a, b), combine_task(b, a)))
_choose_task(task::PriorityTask) = task.task
_choose_task(task) = task
_result_task(a::PriorityTask, b::PriorityTask) = PriorityTask(_result_task(a.task, b.task))
_result_task(a::UnknownTask, b::UnknownTask) = throw(MethodError(combine_task, a, b))
_result_task(a, b::UnknownTask) = a
_result_task(a::UnknownTask, b) = b
_result_task(a::T, b::T) where {T} = (a == b) ? a : @assert false "TODO lower_task_ambiguity_error"
_result_task(a, b) = (a == b) ? a : @assert false "TODO lower_task_ambiguity_error"
combine_task(a, b) = UnknownTask()
combine_task(a::DefaultTask, b::DefaultTask) = DefaultTask()

function transform_reformat(node::Loop, ctx, ::DefaultTask)
    isempty(node.idxs) && return transform_reformat(node.body, ctx)
    push!(ctx.qnt, node.idxs[1])
    push!(ctx.qnt′, node.idxs[1])
    body′ = transform_reformat(Loop(node.idxs[2:end], node.body), ctx)
    pop!(ctx.qnt)
    pop!(ctx.qnt′)
    return Loop(Any[node.idxs[1]], body′)
end

function transform_reformat(node::With, ctx, ::DefaultTask)
    prod = transform_reformat(node.prod, ctx)
    ctx.nest[getresult(node.prod)] = length(ctx.qnts)
    prod = transform_reformat(node.cons, ctx)
    delete!(getresult(node.prod))
end

function transform_reformat(node, ctx, ::DefaultTask)
    if istree(node)
        similarterm(node, operation(node), map(arg -> transform_reformat(arg, ctx), arguments(node)))
    else
        node
    end
end



struct ReformatReadTask
    tns
    keep
    idxs
    protocols
end

struct ReformatWithTask
    tns
    keep
    protocols
end

function transform_reformat_collect(root, ctx::ReformatContext, node::Access{SymbolicHollowDirector})
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        #push a tensor reformat as far down the nest as we can, without computing it redundantly
        keep = findfirst(i->ctx.qnt′[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
        if keep == 1 && haskey(ctx.nest, getname(node.tns))
            if root isa With && getname(getresult(root.prod)) == getname(node.tns)
                return [ReformatWithTask(node.tns.tns, keep, format, protocol)]
            end
        elseif top + keep == length(ctx.qnt)
            return [ReformatReadTask(node.tns.tns, keep, node.idxs[1:keep-1], Set([protocol]))]
        end
    end
    return [DefaultTask()]
end

combine_task(a::ReformatReadTask, b::DefaultTask) = a
function combine_task(a::ReformatReadTask, b::ReformatReadTask)
    if a.tns == b.tns
        return ReformatReadTask(a.tns, min(a.keep, b.keep), intersect(a.idxs, b.idxs), union(a.protocols, b.protocols))
    end
    return PriorityTask(getname(a.tns) < getname(b.tns) ? a : b)
end

function transform_reformat(root, ctx::ReformatContext, task::ReformatReadTask)
    protocols = unzip(task.protocols)
    format′ = [foldl(widenformat, protocols[i], init = NoFormat()) for i = task.keep:length(getformat(task.tns))]
    println((format′, task.tns.format))
    name′ = freshen(getname(task.tns))
    dims′ = task.tns.dims[task.keep:end]
    tns′ = SymbolicHollowTensor(name′, format′, dims′, task.tns.default)
    idxs′ = [Name(gensym()) for _ in format′]
    #for now, assume that a different pass will add "default" read/write protocols
    prod′ = @i (@loop $idxs′ $tns′[$idxs′] = $(task.tns)[$(task.idxs), $idxs′])
    substitute_reformat(node) = node
    function substitute_reformat(node::Access{SymbolicHollowDirector})
        if task.tns == node.tns.tns
            if !all(i -> hasprotocol(getformat(node.tns)[i], getprotocol(node.tns)[i]), 1:length(getformat(node.tns)))
                return Access(SymbolicHollowDirector(tns′, getprotocol(node.tns)[task.keep:end]), node.mode, node.idxs[task.keep:end])
            end
        end
        node
    end
    cons′ = Postwalk(substitute_reformat)(root)
    return With(transform_reformat(cons′), prod′)
end