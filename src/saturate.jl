distributes(a, b) = false
distributes(a::IndexNode, b::IndexNode) = distributes(value(a), value(b))
distributes(a::typeof(+), b::typeof(*)) = true
distributes(a::typeof(+), b::typeof(-)) = true #should use a special operator here to mean "negation"

loopindices(stmt::Loop) = union(loopindices(stmt.body), stmt.idxs)
loopindices(node) = istree(node) ? mapreduce(loopindices, union, push!(arguments(node), nothing)) : []

accessindices(stmt::Access) = collect(stmt.idxs)
accessindices(node) = istree(node) ? mapreduce(accessindices, union, push!(arguments(node), nothing)) : []

reducer(stmt::Assign) = stmt.op
reducer(stmt::Loop) = reducer(stmt.body)
reducer(stmt::With) = reducer(stmt.cons)

assigner(stmt::Assign) = stmt
assigner(stmt::Loop) = assigner(stmt.body)
assigner(stmt::With) = assigner(stmt.cons)

w₀ = Workspace(0)
w₁ = Workspace(1)
w₊ = Postwalk(node -> node isa Workspace ? Workspace(node.n + 1) : node)
w₋(_w) = Postwalk(node -> (node isa Workspace && node.n isa Integer) ? (node.n == 1 ? _w : Workspace(node.n - 1)) : node)

function name_workspaces(prgm)
	w_n = 1
	Postwalk(PassThrough((node) -> if node isa With
        if reducer(node.prod) === nothing
            idxs = intersect(loopindices(node), accessindices(node.prod))
            w_prod = access(Workspace(Symbol("w_$w_n")), Write(), idxs)
        else
            idxs = intersect(loopindices(node), accessindices(node.prod), accessindices(node.cons))
            w_prod = access(Workspace(Symbol("w_$w_n")), Update(), idxs)
        end
	    w_cons = access(Workspace(Symbol("w_$w_n")), Read(), idxs)
	    w_n += 1
	    return With(w₋(w_cons)(node.cons), w₋(w_prod)(node.prod)) #TODO we make a lot of assumptions here. It would be cleaner to insert read/write properties when the with is created.
	end))(prgm)
end

getname(w::Workspace) = w.n


function saturate_index(stmt)
    normalize = Fixpoint(Postwalk(Chain([
        (@ex@rule @i(@loop (~~i) @loop (~~j) ~s) => @i @loop (~~i) (~~j) ~s),
    ])))

    stmt = loop(stmt)
    (@ex@capture normalize(stmt) @i @loop (~~idxs) ~lhs <~~op>= ~rhs) ||
        throw(ArgumentError("expecting statement in index notation"))

    splay = Fixpoint(Postwalk(Chain([
        (@ex@rule @i(+(~a, ~b, ~c, ~~d)) => @i ~a + +(~b, ~c, ~~d)),
        (@ex@rule @i(+(~a)) => ~a),
        (@ex@rule @i(*(~a, ~b, ~c, ~~d)) => @i ~a * *(~b, ~c, ~~d)),
        (@ex@rule @i(*(~a)) => ~a),
        (@ex@rule @i(~a - ~b) => @i ~a + (- ~b)),
        (@ex@rule @i(- (- ~a)) => ~a),
        (@ex@rule @i(- +(~a, ~~b)) => @i +(- ~a, - +(~~b))),
        (@ex@rule @i(*(~~a, - ~b, ~~c)) => @i -(*(~~a, ~b, ~~c))),
    ])))
    rhs = splay(rhs)

    churn = FixpointSaturate(PostwalkSaturate(ChainSaturate([
        (@ex@rule @i(~a + (~b + ~c)) => [@i (~a + ~b) + ~c]),
        (@ex@rule @i(~a + ~b) => [@i ~b + ~a]),
        #(@ex@rule @i(- ~a + (- ~b)) => [@i -(~b + ~a)]),
        #(@ex@rule @i(-(~a + ~b)) => [@i - ~b + (- ~a)]),
        (@ex@rule @i(~a * (~b * ~c)) => [@i (~a * ~b) * ~c]),
        (@ex@rule @i(~a * ~b) => [@i ~b * ~a]),
        #(@ex@rule @i(~a * (- ~b)) => [@i -(~a * ~b)]),
        #(@ex@rule @i(-(~a * ~b)) => [@i (- ~a) * ~b]),
        (@ex@rule @i(~a * (~b + ~c)) => [@i ~a * ~b + ~a * ~c]),
    ])))
    rhss = churn(rhs)

    decommute = Postwalk(Chain([
        (@ex@rule @i(+(~~a)) => if !issorted(~~a) @i +($(sort(~~a))) end),
        (@ex@rule @i(*(~~a)) => if !issorted(~~a) @i *($(sort(~~a))) end),
    ]))

    rhss = unique(map(decommute, rhss))

    bodies = map(rhs->@i($lhs <$op>=$rhs), rhss)

    precompute = PrewalkSaturate(ChainSaturate([
        (x-> if @ex@capture x @i(~Ai <~~f>= ~a)
            bs = FixpointSaturate(PassThroughSaturate(@ex@rule @i((~g)(~~b)) => ~~b))(a)
            ys = []
            for b in bs
                if b != a && @ex @capture b @i((~h)(~~c))
                    d = Postwalk(PassThrough(@ex@rule b => w₀))(a)
                    push!(ys, w₊(@i ($Ai <$f>= $d) where ($w₀ = $b)))
                end
            end
            return ys
        end),
        (x-> if @ex@capture x @i(~Ai <~f>= ~a)
            bs = FixpointSaturate(PassThroughSaturate(@ex@rule @i((~g)(~~b)) =>
                if distributes(f, ~g) ~~b end))(a)
            ys = []
            for b in bs
                if b != a && @ex @capture b @i((~h)(~~c))
                    d = Postwalk(PassThrough(@ex@rule b => w₀))(a)
                    push!(ys, w₊(@i ($Ai <$f>= $d) where ($w₀ <$f>= $b)))
                end
            end
            return ys
        end),
    ]))

    slurp = Fixpoint(Postwalk(Chain([
        (@ex@rule @i(+(~~a, +(~~b), ~~c)) => @i +(~~a, ~~b, ~~c)),
        (@ex@rule @i(+(~a)) => ~a),
        (@ex@rule @i(~a - ~b) => @i ~a + (- ~b)),
        (@ex@rule @i(- (- ~a)) => ~a),
        (@ex@rule @i(- +(~a, ~~b)) => @i +(- ~a, - +(~~b))),
        (@ex@rule @i(*(~~a, *(~~b), ~~c)) => @i *(~~a, ~~b, ~~c)),
        (@ex@rule @i(*(~a)) => ~a),
        (@ex@rule @i(*(~~a, - ~b, ~~c)) => @i -(*(~~a, ~b, ~~c))),
        (@ex@rule @i(+(~~a)) => if !issorted(~~a) @i +($(sort(~~a))) end),
        (@ex@rule @i(*(~~a)) => if !issorted(~~a) @i *($(sort(~~a))) end),
    ])))

    bodies = unique(mapreduce(body->map(slurp, precompute(body)), vcat, bodies))

    prgms = map(body->@i(@loop $idxs $body), bodies)

    #absorb = PassThrough(@ex@rule @i(∀ ~i ∀ ~~j ~s) => @i ∀ $(sort([~i; ~~j])) ~s)

    internalize = PrewalkSaturate(PassThroughSaturate(
        (x) -> if @ex @capture x @i @loop ~~is (~c where ~p)
            #an important assumption of this code is that there are actually no loops in C or P yet that could "absorb" indices.
            if reducer(p) != nothing
                return map(combinations(intersect(is, accessindices(x)))) do js
                    @i @loop $(setdiff(is, js)) (
                        @loop $(intersect(js, accessindices(c))) $c
                    ) where (
                        @loop $(intersect(js, accessindices(p))) $p
                    )
                end
            else
                return map(combinations(intersect(is, accessindices(x)))) do js
                    @i @loop $(setdiff(is, js)) (
                        @loop $js $c
                    ) where (
                        @loop $(intersect(js, accessindices(p))) $p
                    )
                end
            end
        end
    ))
    prgms = mapreduce(internalize, vcat, prgms)
    prgms = map(Postwalk(PassThrough(@ex@rule @i(@loop ~s) => ~s)), prgms)

    reorder = PrewalkSaturate(PassThroughSaturate(
        @ex@rule @i(@loop ~~is ~s) => map(js -> @i(@loop $js ~s), collect(permutations(~~is))[2:end])
    ))

    prgms = mapreduce(reorder, vcat, prgms)
    prgms = map(name_workspaces, prgms)
end

saturate_symaccesses(node) = node
function saturate_symaccesses(node::Access)
    σs = []
    result = []
    for σ in sympermutations(node.idxs)
        tns, σ = retranspose(node.tns, σ)
        if !(σ ∈ σs)
            push!(σs, σ)
            push(result, Access(tns, node.mode, node.idxs[σ]))
        end
    end
    return result
end

saturate_formats(node) = [node]

retranspose(tns, σ) = (tns, σ) #TODO should be error?

struct DimensionalizeWorkspaceContext{Ctx}
    dims
end

function format_workspaces(prgm, Ctx, workspacer)
    ctx = DimensionalizeWorkspaceContext{Ctx}(Dimensions())
    prgm = transform_ssa(prgm)
    Postwalk(node -> (dimensionalize!(node, ctx); node))(prgm)
    dims = ctx.dims
	Postwalk(PassThrough((node) -> if node isa Access{Workspace}
        name = getname(node.tns)
        tns = workspacer(name, node.mode, map(idx->dims[getname(idx)], node.idxs))
	    return access(tns, node.mode, node.idxs)
	end))(prgm)
end

getdims(ctx::DimensionalizeWorkspaceContext) = ctx.dims
lower_axes(::Workspace, ::DimensionalizeWorkspaceContext) = Base.Iterators.repeated(nothing)
getsites(::Workspace) = Base.Iterators.countfrom()

fiber_workspacer(name, mode, dims) = Fiber(name, Any[NoFormat() for _ in dims], dims, 0, collect(1:length(dims))) #TODO assumes default is 0, that might be a problem

bigprotocolize(ex) = Any[ex]
function bigprotocolize(ex::Access{SymbolicHollowTensor, Read})
    tns = ex.tns
    return Any[Access(Direct(tns, collect(protocol)), ex.mode, ex.idxs) for protocol in product([[LocateProtocol(), StepProtocol()] for _ in getformat(tns)]...)]
end

function bigprotocolize(ex::Access{SymbolicHollowTensor})
    Any[Access(Direct(ex.tns, [AppendProtocol() for _ in getformat(ex.tns)]), ex.mode, ex.idxs)] #TODO This is probably wrong, might want to merge with MarkInsertContext
end

#TODO more TACO hacks

noprotocolize(ex) = ex
function noprotocolize(ex::Access{SymbolicHollowTensor, Read})
    tns = ex.tns
    return Access(Direct(tns, [StepProtocol() for _ in getformat(tns)]), ex.mode, ex.idxs) #Should be ignored later
end

function noprotocolize(ex::Access{SymbolicHollowTensor})
    Access(Direct(ex.tns, [AppendProtocol() for _ in getformat(ex.tns)]), ex.mode, ex.idxs)
end

tacoprotocolize(ex) = Any[ex]
function tacoprotocolize(ex::Access{SymbolicHollowDirector, Read})
    tns = ex.tns
    return Any[Access(Direct(tns.tns, [StepProtocol(); [StepProtocol() for _ in getformat(tns)[2:end]]], tns.perm), ex.mode, ex.idxs),
        Access(Direct(tns.tns, [LocateProtocol(); [StepProtocol() for _ in getformat(tns)[2:end]]], tns.perm), ex.mode, ex.idxs)]
end