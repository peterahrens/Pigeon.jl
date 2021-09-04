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

struct SymbolicCoiterableTensor
    name
    default
    implicit #describes whether this tensor initially holds entirely implicit values
end
name(tns::SymbolicCoiterableTensor) = tns.name
SCTensor(name) = SCTensor(name, Literal(0))
SCTensor(name, default) = SymbolicCoiterableTensor(name, default, false)
isimplicit(tns::SymbolicCoiterableTensor) = tns.implicit
implicitize(tns::SymbolicCoiterableTensor) = SymbolicCoiterableTensor(tns.name, tns.default, true)

struct SymbolicLocateTensor
    name
end
name(tns::SymbolicLocateTensor) = tns.name
SLTensor(name) = SymbolicLocateTensor(name)

isimplicit(x) = false

struct ImplicitFiberRelation
    init
    data
    format
    default
end

struct CoiterateRelator end
struct LocateRelator end

#pass in a guard on the iteration
#return the iteration and whatever information should be gleaned from the assignments

struct AsymptoticContext
    qnts::Set{Any}
    bindings::Dict{Any}
    guard::Any
end
AsymptoticContext() = AsymptoticContext(Set(), Dict(), true)

quantify(ctx::AsymptoticContext, vars...) = AsymptoticContext(union(ctx.qnts, vars), ctx.bindings, ctx.guard)
bind(ctx::AsymptoticContext, vars) = AsymptoticContext(ctx.qnts, merge(lower_asymptote_bind_merge, ctx.bindings, vars), ctx.guard)
enguard(ctx::AsymptoticContext, guard) = AsymptoticContext(ctx.qnts, ctx.bindings, Wedge(ctx.guard, guard))

lower_asymptote_merge((iters_a, bindings_a), (iters_b, bindings_b)) =
    (Cup(iters_a, iters_b), merge(lower_asymptote_bind_merge, bindings_a, bindings_b))

lower(::Pass, ::AsymptoticContext, ::DefaultStyle) = (Empty(), Dict())

function lower(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    return (Such(Times(name.(ctx.qnts)...), ctx.guard), Dict())
end

function lower(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return lower(stmt.body, ctx)
    return lower(Loop(stmt.idxs[2:end], stmt.body), quantify(ctx, stmt.idxs[1]))
end

function lower(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    prod_iters, prod_bindings = lower(stmt.prod, ctx)
    cons_iters, cons_bindings = lower(stmt.cons, bind(ctx, prod_bindings))
    return (Cup(prod_iters, cons_iters), cons_bindings)
end

struct CoiterateStyle
    style
end

#TODO handle children of access?
make_style(root::Loop, ctx::AsymptoticContext, node::Access{SymbolicCoiterableTensor}) =
    (!isempty(root.idxs) && root.idxs[1] in node.idxs) ? CoiterateStyle(DefaultStyle()) : DefaultStyle()
combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle(result_style(a.style, b.style))

#TODO generalize the interface to annihilation analysis
annihilate_index = Fixpoint(Postwalk(Chain([
    (@ex@rule i"(~f)(~~a)"p => if isliteral(~f) && all(isliteral, ~~a) Literal(value(~f)(value.(~~a)...)) end),
    (@ex@rule i"+(~~a, +(~~b), ~~c)"p => i"+(~~a, ~~b, ~~c)"c),
    (@ex@rule i"+(~~a)"p => if any(isliteral, ~~a) i"+($(filter(!isliteral, ~~a)), $(Literal(+(value.(filter(isliteral, ~~a))...))))"c end),
    (@ex@rule i"+(~~a, 0, ~~b)"p => i"+(~~a, ~~b)"c),

    (@ex@rule i"*(~~a, *(~~b), ~~c)"p => i"*(~~a, ~~b, ~~c)"c),
    (@ex@rule i"*(~~a)"p => if any(isliteral, ~~a) i"*($(filter(!isliteral, ~~a)), $(Literal(*(value.(filter(isliteral, ~~a))...))))"c end),
    (@ex@rule i"*(~~a, 1, ~~b)"p => i"*(~~a, ~~b)"c),
    (@ex@rule i"*(~~a, 0, ~~b)"p => Literal(0)),

    (@ex@rule i"+(~a)"p => ~a),
    (@ex@rule i"~a - ~b"p => i"~a + - ~b"c),
    (@ex@rule i"- (- ~a)"p => ~a),
    (@ex@rule i"- +(~a, ~~b)"p => i"+(- ~a, - +(~~b))"c),
    (@ex@rule i"*(~a)"p => ~a),
    (@ex@rule i"*(~~a, - ~b, ~~c)"p => i"-(*(~~a, ~b, ~~c))"c),

    #(@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
    #(@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)

    (@ex@rule i"(~a)[~~i] = 0"p => Pass()), #TODO this is only valid when the default of A is 0
    (@ex@rule i"(~a)[~~i] += 0"p => Pass()),
    (@ex@rule i"(~a)[~~i] *= 1"p => Pass()),

    (@ex@rule i"(~a)[~~i] *= ~b"p => if isimplicit(~a) && (~a).default == Literal(0) Pass() end),
    (@ex@rule i"(~a)[~~i] = ~b"p => if isimplicit(~a) && (~a).default == ~b Pass() end),

    (@ex@rule i"∀ (~~i) $(Pass())"p => Pass()),
    (@ex@rule i"$(Pass()) with $(Pass())"p => Pass()),
])))

function lower(stmt::Loop, ctx::AsymptoticContext, ::CoiterateStyle)
    isempty(stmt.idxs) && return ctx(stmt.body)
    ctx′ = quantify(ctx, stmt.idxs[1])
    stmt′ = Loop(stmt.idxs[2:end], stmt.body)
    loop_iters = coiterate_asymptote(stmt, ctx′, stmt′)
    cases = coiterate_cases(stmt, ctx′, stmt′)
    body_iters, body_binds = mapreduce(lower_asymptote_merge, cases) do (guard, body)
            lower(annihilate_index(body), enguard(ctx′, guard))
    end
    return (Cup(loop_iters, body_iters), body_binds)
end

coiterate_asymptote(root, ctx, node) = _coiterate_asymptote(root, ctx, node)
function _coiterate_asymptote(root, ctx, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote(root, ctx, arg), Cup, arguments(node))
    else
        return Empty()
    end
end
function coiterate_asymptote(root, ctx, stmt::Access{SymbolicCoiterableTensor})
    root.idxs[1] in stmt.idxs || return Empty()
    return Such(Times(name.(ctx.qnts)...), coiterate_predicate(ctx, stmt.tns, stmt.idxs))
end

coiterate_cases(root, ctx, node) = _coiterate_cases(root, ctx, node)
function _coiterate_cases(root, ctx, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(root, ctx, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(ctx.guard, node),]
    end
end
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Access{SymbolicCoiterableTensor})
    if !isempty(stmt.idxs) && root.idxs[1] in stmt.idxs
        stmt′ = stmt.mode === Read() ? stmt.tns.default : Access(implicitize(stmt.tns), stmt.mode, stmt.idxs)
        return [(coiterate_predicate(ctx, stmt.tns, stmt.idxs), stmt),
            (ctx.guard, stmt′),]
    else
        return [(ctx.guard, stmt),]
    end
end

#make_style(root::Assign, ctx::AsymptoticContext, node::SymbolicCoiterableTensor) = CoiterateStyle(DefaultStyle(), false)
#function lower(root::Assign, ctx::AsymptoticContext, style::CoiterateStyle)
function lower(root::Assign, ctx::AsymptoticContext, style::DefaultStyle)
    return (Such(Times(name.(ctx.qnts)...), ctx.guard), coiterate_bind(root, ctx, root.lhs.tns))
end
struct BindSite
    n
end
struct SymbolicPattern
    stuff
end
coiterate_predicate(ctx::AsymptoticContext, tns, idxs) = true
function coiterate_predicate(ctx::AsymptoticContext, tns::SymbolicCoiterableTensor, idxs)
    if haskey(ctx.bindings, name(tns))
        rename(n::BindSite) = name(idxs[n.n])
        rename(x) = x
        pattern = Postwalk(PassThrough(rename))(ctx.bindings[name(tns)].stuff)
    else
        pattern = Predicate(name(tns), name.(idxs)...)
    end
    Wedge(ctx.guard, Exists(name.(filter(j->!(j ∈ ctx.qnts), idxs))..., pattern))
end

coiterate_bind(root, ctx, tns) = Dict()
function coiterate_bind(root, ctx, tns::Union{SymbolicCoiterableTensor, SymbolicLocateTensor})
    renamer = Postwalk(PassThrough(idx -> if (n = findfirst(isequal(idx), name.(root.lhs.idxs))) !== nothing BindSite(n) end))
    #TODO doesn't handle A{i, i}
    Dict(name(tns)=>SymbolicPattern(Exists(filter(j->!(j ∈ ctx.qnts), root.lhs.idxs), renamer(ctx.guard))))
end
lower_asymptote_bind_merge(a::SymbolicPattern, b::SymbolicPattern) = SymbolicPattern(Vee(a.stuff, b.stuff))
