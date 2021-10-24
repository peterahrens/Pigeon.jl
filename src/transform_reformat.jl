mutable struct ReformatContext
    nest
    qnt
    qnt′
end

transform_reformat(node) = transform_reformat(node, ReformatContext(Dict(), [], []))

function transform_reformat(root, ctx)
    tasks = transform_reformat_collect(root, ctx, root)
    
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

    #filter out actions that aren't ready yet

    acts = filter(act -> transform_reformat_ready(root, ctx, act), acts)

    println(acts)

    #choose an action to perform

    transform_reformat(root, ctx, foldl(choose_task, acts, init = DefaultTask()))
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
    prod_tasks = transform_reformat_collect(root, ctx, node.prod)
    ctx.nest[getname(getresult(node.prod))] = length(ctx.qnt′)
    cons_tasks = transform_reformat_collect(root, ctx, node.cons)
    delete!(ctx.nest, getname(getresult(node.prod)))
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
_result_task(a::T, b::T) where {T} = a#(a == b) ? a : (println(a, b); @assert false "TODO lower_task_ambiguity_error")
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
    ctx.nest[getname(getresult(node.prod))] = length(ctx.qnt)
    cons = transform_reformat(node.cons, ctx)
    delete!(ctx.nest, getname(getresult(node.prod)))
    return With(cons, prod)
end

function transform_reformat(node, ctx, ::DefaultTask)
    if istree(node)
        similarterm(node, operation(node), map(arg -> transform_reformat(arg, ctx), arguments(node)))
    else
        node
    end
end



struct ReformatLoopTask
    tns
    keep
    mode
    idxs
    protocols
end

struct ReformatWithTask
    tns
    keep
    protocols
end

transform_reformat_ready(root, ctx, ::DefaultTask) = true
function transform_reformat_ready(root, ctx, task::ReformatLoopTask)
    issubset(task.idxs[1:task.keep-1], ctx.qnt)
end
transform_reformat_ready(root, ctx, task::ReformatWithTask) = true

function transform_reformat_collect(root, ctx::ReformatContext, node::Access{SymbolicHollowDirector})
    name = getname(node.tns)
    protocol = getprotocol(node.tns)
    format = getformat(node.tns)
    top = get(ctx.nest, name, 0)
    if !all(i -> hasprotocol(format[i], protocol[i]), 1:length(format))
        #push a tensor reformat as far down the nest as we can, without computing it redundantly
        keep = findfirst(i->ctx.qnt′[top + i] != node.idxs[i] || !hasprotocol(format[i], protocol[i]), 1:length(format))
        if keep == 1 && haskey(ctx.nest, getname(node.tns))
            return [ReformatWithTask(node.tns.tns, format, Set([protocol]))]
        else
            return [ReformatLoopTask(node.tns.tns, keep, node.mode, node.idxs[1:keep-1], Set([protocol]))]
        end
    end
    return [DefaultTask()]
end

combine_task(a::ReformatLoopTask, b::DefaultTask) = a
function combine_task(a::ReformatLoopTask, b::ReformatLoopTask)
    if a.tns == b.tns
        if (a.mode == Read()) ⊻ (b.mode == Read())
            return ReformatWithTask(a.tns, min(a.keep, b.keep), union(a.protocols, b.protocols))
        else
            @assert a.mode == b.mode
            return ReformatLoopTask(a.tns, min(a.keep, b.keep), a.mode, intersect(a.idxs, b.idxs), union(a.protocols, b.protocols))
        end
    end
    return PriorityTask(getname(a.tns) < getname(b.tns) ? a : b)
end

combine_task(a::ReformatWithTask, b::DefaultTask) = a
function combine_task(a::ReformatWithTask, b::ReformatLoopTask)
    if a.tns == b.tns
        return ReformatWithTask(a.tns, min(a.keep, b.keep), union(a.protocols, b.protocols))
    end
    return PriorityTask(a)
end
function combine_task(a::ReformatWithTask, b::ReformatWithTask)
    if a.tns == b.tns
        return ReformatWithTask(a.tns, min(a.keep, b.keep), union(a.protocols, b.protocols))
    end
    return PriorityTask(getname(a.tns) < getname(b.tns) ? a : b)
end

function transform_reformat(root, ctx::ReformatContext, task::ReformatLoopTask)
    protocols = unzip(task.protocols)
    format′ = [foldl(widenformat, protocols[i], init = NoFormat()) for i = task.keep:length(getformat(task.tns))]
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

function transform_reformat(root, ctx::ReformatContext, task::ReformatWithTask)
    protocols = unzip(task.protocols)
    format′ = [foldl(widenformat, protocols[i], init = getformat(task.tns)[i]) for i = 1:length(getformat(task.tns))] #For now we only widen, might make sense to just collect all the protocols for everything at each step.
    tns′ = SymbolicHollowTensor(getname(task.tns), format′, task.tns.dims, task.tns.default)
    #for now, assume that a different pass will add "default" read/write protocols
    substitute_reformat(node) = node
    function substitute_reformat(node::Access{SymbolicHollowDirector})
        if task.tns == node.tns.tns
            if !all(i -> hasprotocol(getformat(node.tns)[i], getprotocol(node.tns)[i]), 1:length(getformat(node.tns)))
                return Access(SymbolicHollowDirector(tns′, getprotocol(node.tns)), node.mode, node.idxs)
            end
        end
        node
    end
    return transform_reformat(Postwalk(substitute_reformat)(root), ctx)
end