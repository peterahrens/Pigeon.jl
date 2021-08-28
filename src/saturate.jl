distributes(a, b) = false
distributes(a::IndexNode, b::IndexNode) = distributes(value(a), value(b))
distributes(a::typeof(+), b::typeof(*)) = true
distributes(a::typeof(+), b::typeof(-)) = true #should use a special operator here to mean "negation"

indices(stmt::Access) = collect(stmt.idxs)
indices(stmt::Loop) = union(indices(stmt.body), stmt.idxs)
indices(node) = istree(node) ? mapreduce(indices, union, push!(arguments(node), nothing)) : []

reducer(stmt::Assign) = stmt.op
reducer(stmt::Loop) = reducer(stmt.body)
reducer(stmt::Where) = reducer(stmt.cons)

w₀ = Workspace(0)
w₁ = Workspace(1)
w₊ = Postwalk(node -> node isa Workspace ? Workspace(node.n + 1) : node)
w₋(_w) = Postwalk(node -> node isa Workspace ? (node.n == 1 ? _w : Workspace(node.n - 1)) : node)

function name_workspaces(prgm)
	w_n = 1
	Postwalk(PassThrough((node) -> if node isa Where
	    w = access(Name(Symbol("w_$w_n")), intersect(indices(node.prod), indices(node.cons)))
	    w_n += 1
	    return w₋(w)(node)
	end))(prgm)
end

function saturate_index(stmt)
    normalize = Fixpoint(Postwalk(Chain([
        (@expand@rule i"∀ ~~i ∀ ~~j ~s" => i"∀ ~~i, ~~j ~s"),
    ])))

    stmt = loop(stmt)
    (@expand@capture normalize(stmt) i"∀ ~~idxs ~lhs ~~op= ~rhs") ||
        throw(ArgumentError("expecting statement in index notation"))

    splay = Fixpoint(Postwalk(Chain([
        (@expand@rule i"+(~a, ~b, ~c, ~~d)" => i"~a + +(~b, ~c, ~~d)"),
        (@expand@rule i"+(~a)" => ~a),
        (@expand@rule i"*(~a, ~b, ~c, ~~d)" => i"~a * *(~b, ~c, ~~d)"),
        (@expand@rule i"*(~a)" => ~a),
        (@expand@rule i"~a - ~b" => i"~a + (- ~b)"),
        (@expand@rule i"- (- ~a)" => ~a),
        (@expand@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
        (@expand@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
    ])))
    rhs = splay(rhs)

    churn = FixpointStep(PostwalkStep(ChainStep([
        (@expand@rule i"~a + (~b + ~c)" => [i"(~a + ~b) + ~c"]),
        (@expand@rule i"~a + ~b" => [i"~b + ~a"]),
        #(@expand@rule i"- ~a + (- ~b)" => [i"-(~b + ~a)"]),
        #(@expand@rule i"-(~a + ~b)" => [i"- ~b + (- ~a)"]),
        (@expand@rule i"~a * (~b * ~c)" => [i"(~a * ~b) * ~c"]),
        (@expand@rule i"~a * ~b" => [i"~b * ~a"]),
        #(@expand@rule i"~a * (- ~b)" => [i"-(~a * ~b)"]),
        #(@expand@rule i"-(~a * ~b)" => [i"(- ~a) * ~b"]),
        (@expand@rule i"~a * (~b + ~c)" => [i"~a * ~b + ~a * ~c"]),
    ])))
    rhss = churn(rhs)

    decommute = Postwalk(Chain([
        (@expand@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end),
        (@expand@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end),
    ]))

    rhss = unique(map(decommute, rhss))

    bodies = map(rhs->i"$lhs $op=$rhs", rhss)

    #here, we only treat the second argument because we already did a bunch of churning earlier to consider different orders

    precompute = PrewalkStep(ChainStep([
        (x-> if @expand@capture x i"~Ai ~~f= ~a"
            bs = FixpointStep(PassThroughStep(@expand@rule i"~g(~~b)" => ~~b))(a)
            ys = []
            for b in bs
                if b != a && @expand @capture b i"~h(~~c)"
                    d = Postwalk(PassThrough(@expand@rule b => w₀))(a)
                    push!(ys, w₊(i"$Ai $f= $d where $w₀ = $b"))
                end
            end
            return ys
        end),
        (x-> if @expand@capture x i"~Ai ~f= ~a"
            bs = FixpointStep(PassThroughStep(@expand@rule i"~g(~~b)" =>
                if distributes(f, ~g) ~~b end))(a)
            ys = []
            for b in bs
                if b != a && @expand @capture b i"~h(~~c)"
                    d = Postwalk(PassThrough(@expand@rule b => w₀))(a)
                    push!(ys, w₊(i"$Ai $f= $d where $w₀ $f= $b"))
                end
            end
            return ys
        end),
    ]))

    slurp = Fixpoint(Postwalk(Chain([
        (@expand@rule i"+(~~a, +(~~b), ~~c)" => i"+(~~a, ~~b, ~~c)"),
        (@expand@rule i"+(~a)" => ~a),
        (@expand@rule i"~a - ~b" => i"~a + (- ~b)"),
        (@expand@rule i"- (- ~a)" => ~a),
        (@expand@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
        (@expand@rule i"*(~~a, *(~~b), ~~c)" => i"*(~~a, ~~b, ~~c)"),
        (@expand@rule i"*(~a)" => ~a),
        (@expand@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
        (@expand@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end),
        (@expand@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end),
    ])))

    bodies = unique(mapreduce(body->map(slurp, precompute(body)), vcat, bodies))

    prgms = map(body->i"∀ $idxs $body", bodies)

    #absorb = PassThrough(@expand@rule i"∀ ~i ∀ ~~j ~s" => i"∀ $(sort([~i; ~~j])) ~s")

    internalize = PrewalkStep(PassThroughStep(
        (x) -> if @expand @capture x i"∀ ~~is (~c where ~p)"
            if reducer(p) != nothing
                return map(combinations(intersect(is, indices(x)))) do js
                    i"""∀ $(setdiff(is, js))
                        ((∀ $(intersect(js, indices(c))) $c)
                      where
                        (∀ $(intersect(js, indices(p))) $p))
                    """
                end
            else
                return map(combinations(intersect(is, indices(p)))) do js
                    i"""∀ $(setdiff(is, js))
                        ((∀ $(intersect(js, indices(c))) $c)
                      where
                        (∀ $js $p))
                    """
                end
            end
        end
    ))
    prgms = mapreduce(internalize, vcat, prgms)
    prgms = map(Postwalk(PassThrough(@expand@rule i"∀ $(())... ~s" => ~s)), prgms)

    reorder = PrewalkStep(PassThroughStep(
        @expand@rule i"∀ ~~is ~s" => map(js-> i"∀ $js ~s", permutations(~~is))
    ))

    return map(name_workspaces, mapreduce(reorder, vcat, prgms))
end