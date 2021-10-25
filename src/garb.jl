#TODO this assumes arguments are unique
function enumerate_schedules_old(stmt)
	normalize = Fixpoint(Postwalk(Chain([
	    (@ex@rule i"+(~a, ~b, ~c, ~~d)" => i"~a + +(~b, ~c, ~~d)"),
	    (@ex@rule i"+(~a)" => ~a),
	    (@ex@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@ex@rule i"- (- ~a)" => ~a),
	    (@ex@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@ex@rule i"*(~a, ~b, ~c, ~~d)" => i"~a * *(~b, ~c, ~~d)"),
	    (@ex@rule i"*(~a)" => ~a),
	    (@ex@rule i"∀ ~i, ~j, ~~k ~s" => i"∀ ~i ∀ ~j, ~~k ~s"),
	    (@ex@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    #(@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
	    #(@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)
	])))
	stmt = normalize(stmt)
	universe = Set()
	postorder(node->(push!(universe, node); node), stmt)
    
	function step(node)
	    if istree(node)
		stepped = false
		args′ = map(arguments(node)) do arg
		    if !stepped
			(stepped′, arg′) = step(arg)
			stepped |= stepped′
			return arg′
		    else
			return arg
		    end
		end
		if stepped
		    node′ = normalize(operation(node)(args′))
		    push!(universe, node′)
		    return (true, node′)
		end
	    end
	    for transform in [
		(@ex@rule i"~a + (~b + ~c)" => i"(~a + ~b) + ~c"),
		(@ex@rule i"(~a + ~b) + ~c" => i"~a + (~b + ~c)"),
		(@ex@rule i"~a + ~b" => i"~b + ~a"),
		(@ex@rule i"~a * (~b * ~c)" => i"(~a * ~b) * ~c"),
		(@ex@rule i"(~a * ~b) * ~c" => i"~a * (~b * ~c)"),
		(@ex@rule i"~a * ~b" => i"~b * ~a"),
		(@ex@rule i"∀ ~i ∀ ~j ~s" => i"∀ ~j ∀ ~i ~s"),
		(@ex@rule i"~Ai ~~f= ~g(~a, ~h(~~b))" =>
		    w₊(i"~Ai ~~f= ~g(~a, $w₀) with $w₀ = ~h(~~b)")),
		(@ex@rule i"~Ai += +(~a, ~f(~~b))" =>
		    w₊(i"~Ai += +(~a, $w₀) with $w₀ += ~f(~~b)")),
		(@ex@rule i"~Ai += *(~a, ~f(~~b))" =>
		    w₊(i"~Ai += *(~a, $w₀) with $w₀ += ~f(~~b)")),
		(@ex@rule i"∀ ~i (~c with ~p)" => if (~i in indices(~c)) && !(~i in indices(~p))
		    i"(∀ ~i ~c) with ~p" end),
		(@ex@rule i"∀ ~i (~c with ~p)" => if (~i in indices(~c)) && (~i in indices(~p))
		    i"(∀ ~i ~c) with (∀ ~i ~p)" end),
		(@ex@rule i"∀ ~i (~Ai += ~b * $w₁ with ~p)" => if !(~i in indices(i"~Ai += ~b * $w₁")) && (~i in indices(~p))
		    i"~Ai += ~b * $w₁ with (∀ ~i ~p)" end),
	    ]
		node′ = transform(node)
		if node′ !== nothing && !(node′ in universe)
		    postorder(subnode -> (push!(universe, subnode); subnode), node′)
		    return (true, node′)
		end
	    end
	    return (false, node)
	end
    
	frontier = Any[stmt]
	result = Any[stmt]
    
	simplify = Fixpoint(Postwalk(Chain([
	    (@ex@rule i"+(~~a, +(~~b), ~~c)" => i"+(~~a, ~~b, ~~c)"),
	    (@ex@rule i"+(~a)" => ~a),
	    (@ex@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@ex@rule i"- (- ~a)" => ~a),
	    (@ex@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@ex@rule i"*(~~a, *(~~b), ~~c)" => i"*(~~a, ~~b, ~~c)"),
	    (@ex@rule i"*(~a)" => ~a),
	    (@ex@rule i"∀ ~~i ∀ ~~j ~s" => i"∀ ~~i, ~~j ~s"),
	    (@ex@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    (@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end),
	    (@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end),
	])))
    
	while !isempty(frontier)
	    stmt = pop!(frontier)
    
	    while true
		(stepped, stmt′) = step(stmt)
		if stepped
		    push!(frontier, stmt′)
		    push!(result, name_workspaces(stmt′))
		else
		    break
		end
	    end
	end
	return unique(map(simplify, result))
    end 
 
    #=
struct Initial <: IndexStatement
	op::Any
	val::Any
end
Base.:(==)(a::Initial, b::Initial) = a.op == b.op && a.val == b.val

initial(args...) = initial!(vcat(args...))
function initial!(args)
    @assert length(args) == 2
    return Initial(args[1], args[2])
end

SymbolicUtils.istree(ex::Initial) = true
SymbolicUtils.operation(ex::Initial) = initial
SymbolicUtils.arguments(ex::Initial) = [ex.op, ex.val]
SymbolicUtils.similarterm(::IndexNode, ::typeof(initial), args, T...) = initial!(args)

function show_expression(io, mime, ex::Initial, level)
    show_expression(io, mime, ex.lhs)
    print(io, "(")
    print(io, ex.op)
    print(io, ", ")
    print(io, ex.val)
    print(io, ")")
end
=#

# What to change?
#
# (A) We want to make the coiterate_case function able to dispatch access handling based on tensors
# options:
#   1. rewrite rule dispatch (do a pass to collect rules, match in context you want, check concrete types)
#      pros: 
#           can express a wide variety of patterns, including the one we want
#           we probably need to use some version of this for annihilation anyway
#      cons:
#           the common case is complicated
#           dispatch is order-dependent
#   2. type-based dispatch (type the tree)
#      Pros:
#           expressing the dispatch we want is a one-liner
#      Cons:
#           There's nothing to enforce that dispatch can become ambiguous
#   3. delay matching (tensor declares result that gets unpacked into access later)
#   3 (continued). give a list of parents to the visitor function
#       Pros:
#           Dispatch is a one-liner
#       Cons:
#           delays are confusing to implement
#   4. make tensors responsible for holding indices
#       Pros:
#           Dispatch is super clear and straightforward
#           Makes some semantic sense
#       Cons:
#           There's no good interface for if indices are shifted or something (in dense case)
#           Tensors need to implement more complicated functions
#   5. use special Access types
#       Pros:
#           Dispatch is super clear and straightforward
#           No ambiguities because Accesses and References are typed by their tensor
#           Common case is easy
#           This is sortof like 4, with nice defaults. I'm choosing 4. We might do the same thing for accesses.
#       Cons:
#           Doesn't solve more complicated dispatch problems (How to dispatch access lowering? probably style resolution let's be honest)
#           Sortof confusing because every implementation needs to do the same boilerplate to lower indices (is there any solution that avoids this?)
#   6. use style resolution at every level
#       Pros:
#           consistent
#       Cons:
#           messy
#           sorta makes most sense for forall, where, and assign statements, not access statements, which usually feel very terminal
#   7. need to differentiate lhs from rhs access
#       Could use "reference" type, could pass in a "write" parameter in traversals, some context-based approaches help too.
#       I like the "reference" type because it's clean, but it's unclear if Access{Any} is more specific than Union{Access{T}, Reference{T}}
#       What if we pass in a write or read parameter into the Access?
#       Access{Tns, true} vs Access{Tns, false} ?
#   Notes: What we're dealing with is that tensors belong more to the access
#   node itself than to the children of the access, and that it's more
#   convenient to treat them as terminals (indices cannot be functions). Indices
#   usually aren't functions, but if they are, we sorta have bigger problems no?
#   You won't get your Ph.D. if you handle indices that are functions.
#   Notes: styles should move through an "access style resolution" step if we are gonna make this work.
# come back to (A)
# We want to handle global iteration counting and contexts with mutability rather than functionally (cleaner)
# We want to simplify assignments to references known to be entirely implicit
# We want to initialize workspaces
# We need tests


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
