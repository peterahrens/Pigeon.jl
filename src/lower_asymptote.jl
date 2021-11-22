function saturate_formats(tns::AbstractSymbolicHollowTensor)
    result = []
    for format in product(tns.format...) #TODO (This isn't even covered in tests I don't think. Hmmm...)
        tns′ = copy(tns)
        tns′.format = collect(format) #TODO
        push!(result, tns′)
    end
    result
end

const Fiber = SymbolicHollowTensor
const Dense = SymbolicSolidTensor
const Direct = SymbolicHollowDirector

struct ImplicitSymbolicHollowTensor <: AbstractSymbolicHollowTensor
    tns
end

getname(tns::ImplicitSymbolicHollowTensor) = getname(tns.tns)
getdatadefault(tns::ImplicitSymbolicHollowTensor, ctx) = getdatadefault(tns.tns, ctx)
getprotocol(tns::ImplicitSymbolicHollowTensor) = getprotocol(tns.tns)
getdefault(tns::ImplicitSymbolicHollowTensor) = getdefault(tns.tns)
getsites(tns::ImplicitSymbolicHollowTensor) = getsites(tns.tns)
lower_axes(tns::ImplicitSymbolicHollowTensor, ctx) = lower_axes(tns.tns, ctx)

isimplicit(tns) = false
isimplicit(::ImplicitSymbolicHollowTensor) = true

mutable struct AsymptoticContext
    itrs::Any
    qnts::Vector{Any}
    guards::Vector{Any}
    state::Dict
    dims
end

function getdata(tns::AbstractSymbolicHollowTensor, ctx::AsymptoticContext)
    get!(ctx.state, getname(tns), getdatadefault(tns, ctx))
end

function getdatadefault(tns::SymbolicHollowTensor, ctx::AsymptoticContext)
    PointQuery(Predicate(getname(tns), [CanonVariable(n) for n in 1:length(getsites(tns))]...))
end

function getdatadefault(tns::SymbolicHollowDirector, ctx::AsymptoticContext)
    PointQuery(Predicate(getname(tns), [CanonVariable(n) for n in 1:length(getsites(tns))]...))
end

lower_axes(tns::SymbolicHollowDirector, ctx) = lower_axes(tns.tns, ctx)[getsites(tns)]
lower_axes(tns::SymbolicHollowTensor, ::AsymptoticContext) = tns.dims
lower_axes(tns::SymbolicHollowTensor, ::DimensionalizeWorkspaceContext{AsymptoticContext}) = tns.dims
lower_axes(tns::SymbolicSolidTensor, ::AsymptoticContext) = tns.dims
lower_axes(tns::SymbolicSolidTensor, ::DimensionalizeWorkspaceContext{AsymptoticContext}) = tns.dims
lower_axis_merge(::AsymptoticContext, a, b) = (@assert a == b; b)
lower_axis_merge(::DimensionalizeWorkspaceContext{AsymptoticContext}, a, b) = (@assert a == b; b)

AsymptoticContext() = AsymptoticContext(Empty(), [], [true], Dict(), Dimensions())

getdims(ctx::AsymptoticContext) = ctx.dims

function asymptote(prgm, ctx = AsymptoticContext())
    #TODO messy
    prgm = transform_ssa(prgm)
    visit!(prgm, ctx)
    return ctx.itrs
end

function read_cost(tns::AbstractSymbolicHollowTensor, ctx = AsymptoticContext())
    idxs = [gensym() for _ in getsites(tns)]
    pred = getdata(tns, ctx)[Name.(idxs)...]
    return Such(Times(Domain.(idxs, tns.dims)...), pred)
end

function read_cost(tns::SymbolicSolidTensor, ctx = AsymptoticContext())
    idxs = [gensym() for _ in tns.dims]
    return Times(Domain.(idxs, tns.dims)...)
end

function assume_nonempty(tns::AbstractSymbolicHollowTensor)
    idxs = [gensym() for _ in getsites(tns)]
    return Exists(idxs..., Predicate(getname(tns), idxs...))
end

iterate!(ctx) = iterate!(ctx, true)
function iterate!(ctx, cond)
    qnts = map(qnt->Domain(getname(qnt), ctx.dims[getname(qnt)]), ctx.qnts)
    ctx.itrs = Cup(ctx.itrs, Such(Times(qnts...), Wedge(guard(ctx), cond)))
end

quantify(f, ctx, var) = (push!(ctx.qnts, var); f(); pop!(ctx.qnts))
enguard(f, ctx, cond) = (push!(ctx.guards, cond); f(); pop!(ctx.guards))
guard(ctx) = reduce(Wedge, ctx.guards)

visit!(::Pass, ::AsymptoticContext, ::DefaultStyle) = nothing

#assumes unique foralls
function visit!(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
end

function visit!(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return visit!(stmt.body, ctx)
    quantify(ctx, stmt.idxs[1]) do
        iterate!(ctx)
        visit!(Loop(stmt.idxs[2:end], stmt.body), ctx)
    end
end

function visit!(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    initialize!(getresult(stmt.prod), ctx)
    visit!(stmt.prod, ctx)
    visit!(stmt.cons, ctx)
end

struct CoiterateStyle
end

#TODO handle children of access?
function make_style(root, ctx::AsymptoticContext, node::Access{<:AbstractSymbolicHollowTensor})
    isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
    return DefaultStyle()
end

function make_style(root, ctx::AsymptoticContext, node::Access{SymbolicSolidTensor})
    isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
    return DefaultStyle()
end

function make_style(root::Loop, ctx::AsymptoticContext, node::Access{<:AbstractSymbolicHollowTensor})
    isdimensionalized(getdims(ctx), node) || return DimensionalizeStyle()
    isempty(root.idxs) && return DefaultStyle()
    i = findfirst(isequal(root.idxs[1]), node.idxs)
    (i !== nothing && node.idxs[1:i-1] ⊆ ctx.qnts) || return DefaultStyle()
    return make_style_protocol(root, ctx, node, getprotocol(node.tns)[i])
end

make_style_protocol(root::Loop, ctx::AsymptoticContext, node, ::LocateProtocol) = DefaultStyle()
make_style_protocol(root::Loop, ctx::AsymptoticContext, node, ::StepProtocol) = CoiterateStyle()
make_style_protocol(root::Loop, ctx::AsymptoticContext, node, ::AppendProtocol) = DefaultStyle()
make_style_protocol(root::Loop, ctx::AsymptoticContext, node, ::InsertProtocol) = DefaultStyle()

combine_style(a::CoiterateStyle, b::CoiterateStyle) = CoiterateStyle()
combine_style(a::CoiterateStyle, b::DimensionalizeStyle) = DimensionalizeStyle()
combine_style(a::DefaultStyle, b::DimensionalizeStyle) = DimensionalizeStyle()
combine_style(a::DimensionalizeStyle, b::DimensionalizeStyle) = DimensionalizeStyle()

#TODO generalize the interface to annihilation analysis
annihilate_index = Fixpoint(Prewalk(Chain([
    (@ex@rule @i((~f)(~~a)) => if isliteral(~f) && all(isliteral, ~~a) Literal(value(~f)(value.(~~a)...)) end),
    (@ex@rule @i((~~a, +(~~b), ~~c)) => @i +(~~a, ~~b, ~~c)),
    (@ex@rule @i(+(~~a)) => if count(isliteral, ~~a) >= 2 @i +($(filter(!isliteral, ~~a)), $(Literal(+(value.(filter(isliteral, ~~a))...)))) end),
    (@ex@rule @i(+(~~a, 0, ~~b)) => @i +(~~a, ~~b)),

    (@ex@rule @i(*(~~a, *(~~b), ~~c)) => @i *(~~a, ~~b, ~~c)),
    (@ex@rule @i(*(~~a)) => if count(isliteral, ~~a) >= 2 @i(*($(filter(!isliteral, ~~a)), $(Literal(*(value.(filter(isliteral, ~~a))...))))) end),
    (@ex@rule @i(*(~~a, 1, ~~b)) => @i *(~~a, ~~b)),
    (@ex@rule @i(*(~~a, 0, ~~b)) => 0),

    (@ex@rule @i(+(~a)) => ~a),
    (@ex@rule @i(~a - ~b) => @i ~a + - ~b),
    (@ex@rule @i(- (- ~a)) => ~a),
    (@ex@rule @i(- +(~a, ~~b)) => @i +(- ~a, - +(~~b))),
    (@ex@rule @i(*(~a)) => ~a),
    (@ex@rule @i(*(~~a, - ~b, ~~c)) => @i -(*(~~a, ~b, ~~c))),

    #(@ex@rule @i(+(~~a)) => if !issorted(~~a) @i +($(sort(~~a))) end),
    #(@ex@rule @i(*(~~a)) => if !issorted(~~a) @i *($(sort(~~a))) end),

    (@ex@rule @i((~a)[~~i] = 0) => pass(~a)), #TODO this is only valid when the default of A is 0
    (@ex@rule @i((~a)[~~i] += 0) => pass(~a)),
    (@ex@rule @i((~a)[~~i] *= 1) => pass(~a)),

    (@ex@rule @i((~a)[~~i] *= ~b) => if isimplicit(~a) && getdefault(~a) == 0 pass(~a) end),
    (@ex@rule @i((~a)[~~i] = ~b) => if isimplicit(~a) && getdefault(~a) == ~b pass(~a) end),
    ((a) -> if a isa Literal && isliteral(value(a)) value(a) end), #only quote when necessary

    (@ex@rule @i(@loop (~~i) @pass(~~a)) => pass(~~a)),
    (@ex@rule @i(@pass(~~a) where ~x) => pass(~~a)),
    #(@ex@rule @i(~x where @pass(~~a)) => ~x), #can't do this bc produced tensors won't get initialized
])))

function visit!(stmt::Loop, ctx::AsymptoticContext, ::CoiterateStyle)
    isempty(stmt.idxs) && return ctx(stmt.body)
    quantify(ctx, stmt.idxs[1]) do
        stmt′ = Loop(stmt.idxs[2:end], stmt.body)
        cases = coiterate_cases(stmt, ctx, stmt′)
        for (guard, body) in cases
            enguard(ctx, guard) do
                visit!(annihilate_index(body), ctx)
            end
        end
        coiterate_asymptote!(stmt, ctx, stmt′)
    end
end

function coiterate_asymptote!(root, ctx, node)
    if istree(node)
        return mapreduce(arg->coiterate_asymptote!(root, ctx, arg), Cup, arguments(node))
    else
        return Empty()
    end
end

function coiterate_asymptote!(root, ctx, stmt::Access{<:AbstractSymbolicHollowTensor})
    i = findfirst(isequal(root.idxs[1]), stmt.idxs)
    (i !== nothing && stmt.idxs[1:i] ⊆ ctx.qnts) || return Empty()
    getprotocol(stmt.tns)[i] === coiter || return Empty() #TODO this line isn't extensible
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs[getsites(stmt.tns)]...])
    return iterate!(ctx, pred)
end

function coiterate_cases(root, ctx, node)
    if istree(node)
        map(product(map(arg->coiterate_cases(root, ctx, arg), arguments(node))...)) do case
            (guards, bodies) = zip(case...)
            (reduce(Wedge, guards), operation(node)(bodies...))
        end
    else
        [(true, node),]
    end
end
function coiterate_cases(root, ctx::AsymptoticContext, stmt::Access{<:AbstractSymbolicHollowTensor})
    single = [(true, stmt),]
    i = findfirst(isequal(root.idxs[1]), stmt.idxs)
    (i !== nothing && stmt.idxs[1:i] ⊆ ctx.qnts) || return single
    getprotocol(stmt.tns)[i] === coiter || return single
    stmt′ = stmt.mode === Read() ? getdefault(stmt.tns) : Access(ImplicitSymbolicHollowTensor(stmt.tns), stmt.mode, stmt.idxs)
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs[getsites(stmt.tns)]...])
    return [(pred, stmt), (true, stmt′),]
end

function visit!(root::Assign{<:Access{<:AbstractSymbolicHollowTensor}}, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
    pred = Exists(getname.(setdiff(ctx.qnts, root.lhs.idxs))..., guard(ctx))
    getdata(root.lhs.tns, ctx)[root.lhs.idxs[getsites(root.lhs.tns)]...] = pred
end

function initialize!(tns::SymbolicHollowDirector, ctx::AsymptoticContext)
    initialize!(tns.tns, ctx)
end
function initialize!(tns::SymbolicHollowTensor, ctx::AsymptoticContext)
    ctx.state[getname(tns)] = PointQuery(false)
end

mutable struct MaxDepthContext
    d_max
    d
end
function maxdepth(prgm)
    ctx = MaxDepthContext(0, 0)
    maxdepth!(prgm, ctx)
    return ctx.d_max
end
function maxdepth!(node, ctx::MaxDepthContext)
    if istree(node)
        map(arg->maxdepth!(arg, ctx::MaxDepthContext), arguments(node))
    end
end
function maxdepth!(node::Loop, ctx::MaxDepthContext)
    ctx.d += length(node.idxs)
    ctx.d_max = max(ctx.d_max, ctx.d)
    maxdepth!(node.body, ctx)
    ctx.d -= length(node.idxs)
end

mutable struct MaxWorkspaceContext
    d_max
end
function maxworkspace(prgm)
    ctx = MaxWorkspaceContext(0)
    maxworkspace!(prgm, ctx)
    return ctx.d_max
end
function maxworkspace!(node, ctx::MaxWorkspaceContext)
    if istree(node)
        map(arg->maxworkspace!(arg, ctx::MaxWorkspaceContext), arguments(node))
    end
end
function maxworkspace!(node::Access{Workspace}, ctx::MaxWorkspaceContext)
    ctx.d_max = max(ctx.d_max, length(node.idxs))
end

mutable struct MaxInsertContext
    d_max
end
function maxinsert(prgm)
    ctx = MaxInsertContext(0)
    maxinsert!(prgm, ctx)
    return ctx.d_max
end
function maxinsert!(node, ctx::MaxInsertContext)
    if istree(node)
        map(arg->maxinsert!(arg, ctx::MaxInsertContext), arguments(node))
    end
end
function maxinsert!(node::Access{SymbolicHollowDirector, <:Union{Write, Update}}, ctx::MaxInsertContext)
    i = findfirst(isequal(InsertProtocol()), getprotocol(node.tns))
    i = i === nothing ? length(getprotocol(node.tns)) + 1 : i
    i = length(getprotocol(node.tns)) - i + 1
    ctx.d_max = max(ctx.d_max, i)
end