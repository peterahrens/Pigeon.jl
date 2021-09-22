distributes(a, b) = false
distributes(a::IndexNode, b::IndexNode) = distributes(value(a), value(b))
distributes(a::typeof(+), b::typeof(*)) = true
distributes(a::typeof(+), b::typeof(-)) = true #should use a special operator here to mean "negation"

indices(stmt::Access) = collect(stmt.idxs)
indices(stmt::Loop) = union(indices(stmt.body), stmt.idxs)
indices(node) = istree(node) ? mapreduce(indices, union, push!(arguments(node), nothing)) : []

reducer(stmt::Assign) = stmt.op
reducer(stmt::Loop) = reducer(stmt.body)
reducer(stmt::With) = reducer(stmt.cons)

w₀ = Workspace(0)
w₁ = Workspace(1)
w₊ = Postwalk(node -> node isa Workspace ? Workspace(node.n + 1) : node)
w₋(_w) = Postwalk(node -> (node isa Workspace && node.n isa Integer) ? (node.n == 1 ? _w : Workspace(node.n - 1)) : node)

function name_workspaces(prgm)
	w_n = 1
	Postwalk(PassThrough((node) -> if node isa With
        idxs = intersect(indices(node.prod), indices(node.cons))
	    w = access(Workspace(Symbol("w_$w_n")), Update(), idxs)
	    w_n += 1
	    return w₋(w)(node)
	end))(prgm)
end

getname(w::Workspace) = w.n

struct DimensionalizeWorkspaceContext{Ctx}
    dims
end

function format_workspaces(prgm, Ctx, workspacer)
    ctx = DimensionalizeWorkspaceContext{Ctx}(Dimensions())
    prgm = transform_ssa(prgm)
    Postwalk(node -> (dimensionalize!(node, ctx); node))(prgm)
    dims = ctx.dims
	Postwalk(PassThrough((node) -> if node isa Access{Workspace}
        name = Name(node.tns)
        tns = workspacer(name, map(idx->dims[getname(idx)], node.idxs))
	    return access(tns, node.mode, node.idxs)
	end))(prgm)
end


getdims(ctx::DimensionalizeWorkspaceContext) = ctx.dims
lower_axes(::Workspace, ::DimensionalizeWorkspaceContext) = Base.Iterators.repeated(nothing)
lower_sites(::Workspace) = Base.Iterators.countfrom()

function saturate_index(stmt, Ctx; workspacer=(name, dims)->name)
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

    churn = FixpointStep(PostwalkStep(ChainStep([
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

    precompute = PrewalkStep(ChainStep([
        (x-> if @ex@capture x @i(~Ai <~~f>= ~a)
            bs = FixpointStep(PassThroughStep(@ex@rule @i((~g)(~~b)) => ~~b))(a)
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
            bs = FixpointStep(PassThroughStep(@ex@rule @i((~g)(~~b)) =>
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

    internalize = PrewalkStep(PassThroughStep(
        (x) -> if @ex @capture x @i @loop ~~is (~c where ~p)
            if reducer(p) != nothing
                return map(combinations(intersect(is, indices(x)))) do js
                    @i @loop $(setdiff(is, js)) (
                        @loop $(intersect(js, indices(c))) $c
                    ) where (
                        @loop $(intersect(js, indices(p))) $p
                    )
                end
            else
                return map(combinations(intersect(is, indices(p)))) do js
                    @i @loop $(setdiff(is, js)) (
                        @loop $(intersect(js, indices(c))) $c
                    ) where (
                        @loop $js $p
                    )
                end
            end
        end
    ))
    prgms = mapreduce(internalize, vcat, prgms)
    prgms = map(Postwalk(PassThrough(@ex@rule @i(@loop ~s) => ~s)), prgms)

    reorder = PrewalkStep(PassThroughStep(
        @ex@rule @i(@loop ~~is ~s) => map(js -> @i(@loop $js ~s), collect(permutations(~~is))[2:end])
    ))

    prgms = mapreduce(reorder, vcat, prgms)
    prgms = map(name_workspaces, prgms)
    return map(node->format_workspaces(node, Ctx, workspacer), prgms)
end

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

retranspose(tns, σ) = (tns, σ)