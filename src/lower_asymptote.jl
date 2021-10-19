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

function show_expression(io, mime, ex::StepProtocol)
    print(io, "c")
end
function show_expression(io, mime, ex::LocateProtocol)
    print(io, "l")
end

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
    PointQuery(Predicate(getname(tns), [CanonVariable(n) for n in tns.perm]...))
end

function getdatadefault(tns::SymbolicHollowDirector, ctx::AsymptoticContext)
    getdatadefault(tns.tns, ctx)
end

lower_axes(tns::SymbolicHollowDirector, ctx) = lower_axes(tns.tns, ctx)[tns.perm]
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
    lower!(prgm, ctx)
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

lower!(::Pass, ::AsymptoticContext, ::DefaultStyle) = nothing

#assumes unique foralls
function lower!(root::Assign, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
end

function lower!(stmt::Loop, ctx::AsymptoticContext, ::DefaultStyle)
    isempty(stmt.idxs) && return lower!(stmt.body, ctx)
    quantify(ctx, stmt.idxs[1]) do
        iterate!(ctx)
        lower!(Loop(stmt.idxs[2:end], stmt.body), ctx)
    end
end

function lower!(stmt::With, ctx::AsymptoticContext, ::DefaultStyle)
    initialize!(getresult(stmt.prod), ctx)
    lower!(stmt.prod, ctx)
    lower!(stmt.cons, ctx)
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

function lower!(stmt::Loop, ctx::AsymptoticContext, ::CoiterateStyle)
    isempty(stmt.idxs) && return ctx(stmt.body)
    quantify(ctx, stmt.idxs[1]) do
        stmt′ = Loop(stmt.idxs[2:end], stmt.body)
        cases = coiterate_cases(stmt, ctx, stmt′)
        for (guard, body) in cases
            enguard(ctx, guard) do
                lower!(annihilate_index(body), ctx)
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
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs...])
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
    pred = Exists(getname.(setdiff(stmt.idxs, ctx.qnts))..., getdata(stmt.tns, ctx)[stmt.idxs...])
    return [(pred, stmt), (true, stmt′),]
end

function lower!(root::Assign{<:Access{<:AbstractSymbolicHollowTensor}}, ctx::AsymptoticContext, ::DefaultStyle)
    iterate!(ctx)
    pred = Exists(getname.(setdiff(ctx.qnts, root.lhs.idxs))..., guard(ctx))
    getdata(root.lhs.tns, ctx)[root.lhs.idxs...] = pred
end

function initialize!(tns::SymbolicHollowDirector, ctx::AsymptoticContext)
    initialize!(tns.tns, ctx)
end
function initialize!(tns::SymbolicHollowTensor, ctx::AsymptoticContext)
    ctx.state[getname(tns)] = PointQuery(false)
end

using Random

dominate_calls = 0

function filter_pareto(kernels; sunk_costs=[], assumptions=[])
    pareto = []
    lower_time = 0
    supersimplify_time = 0
    filter_time = 0
    global simplify_time = 0
    global normalize_time = 0
    global normalize_calls = 0
    global dominate_calls = 0
    asymptotes = @showprogress 0.1 "analysis..." map(kernel->begin
        #supersimplify_asymptote(Cup(asymptote(kernel), sunk_costs...))
        lower_time += @elapsed a = asymptote(kernel)
        a = Such(Cup(a, sunk_costs...), Wedge(assumptions...))
        supersimplify_time += @elapsed a = supersimplify_asymptote(a)
        #supersimplify_time += @elapsed a = normalize_asymptote(Cup(a, sunk_costs...))
        a;
    end, kernels)
    #foreach(display, asymptotes)
    @showprogress 1 "filtering..." for (a, asy_a) in collect(zip(kernels, asymptotes))[randperm(end)]
        pareto′ = Any[(a, asy_a)]
        filter_time += @elapsed begin
            keep = true
            for (b, asy_b) in pareto
                dom_a = isdominated(asy_a, asy_b, normal=true)
                dom_b = isdominated(asy_b, asy_a, normal=true)
                if dom_b && !dom_a
                    keep = false
                    break
                elseif !(dom_a && !dom_b)
                    push!(pareto′, (b, asy_b))
                end
            end
            if keep
                pareto = pareto′
            end
        end
    end

    @info "breakdown" lower_time supersimplify_time filter_time simplify_time normalize_time normalize_calls normalize_time/normalize_calls dominate_calls
    return first.(pareto)
end
