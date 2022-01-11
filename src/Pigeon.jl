module Pigeon

using RewriteTools
using SyntaxInterface
using SyntaxInterface: arguments, operation, istree, similarterm
using RewriteTools: Fixpoint, Chain, Postwalk, Prewalk, PassThrough
using RewriteTools: @rule, @capture
using Random
using Scratch

using Base.Iterators: product
using Combinatorics
using DataStructures
using ProgressMeter

export @i
export @name

export IndexNode, IndexStatement, IndexExpression
export Loop, Assign, With, Access, Call
export loop, assign, with, access, call
export Pass, Literal, Workspace, Name
export postorder, value, name
export postmap, postmapreduce

export Dense, Fiber, Direct
export ListFormat, ArrayFormat, HashFormat, NoFormat
export LocateProtocol, StepProtocol, ConvertProtocol

export saturate_index
export normalize_index
export asymptote
export filter_pareto
export simplify_asymptote
export supersimplify_asymptote

include("utils.jl")
include("index.jl")
include("parse_index.jl")
include("asymptote.jl")

include("tensor.jl")

include("style.jl")
include("saturate.jl")
include("transform_reformat.jl")
include("transform_concordize.jl")
include("transform_normalize.jl")
include("transform_ssa.jl")
include("dimensionalize.jl")
include("lower_asymptote.jl")
include("containment.jl")

#Hacky files for paper
include("taco.jl")

function snoop()
    saturate_index(@i @loop i j k A[i] += B[j] * C[j] * D[k] * E[k])
    saturate_index(@i @loop i j k A[i, j] = B[i, k] * C[k, j] * x[j])
    saturate_index(@i @loop i j A[i] = (-B[j]) * C[j] + D[k])
end

macro name(args::Symbol...)
    return Expr(:block, map(arg->:($(esc(arg)) = Name($(QuoteNode(arg)))), args)..., :(($(map(esc, args)...), )))
end

function autoschedule(prgm; sunk_costs = [], assumptions = [], protocolize = bigprotocolize)
    frontier = saturate_index(prgm)
    #frontier = filter(kernel->maxworkspace(kernel) <= 1, frontier)#TODO TACO LIMITATION
    frontier = filter_pareto(frontier, by = kernel -> maxdepth(kernel))
    frontier = map(prgm->format_workspaces(prgm, AsymptoticContext, fiber_workspacer), frontier)
    frontier = mapreduce(PostwalkSaturate(protocolize), vcat, frontier)
    frontier = map(Pigeon.concordize, frontier)
    frontier = map(prgm -> transform_reformat(prgm, MarkInsertContext()), frontier)
    frontier = filter_pareto(frontier, 
        by = kernel -> supersimplify_asymptote(Such(Cup(asymptote(kernel), sunk_costs...), Wedge(assumptions...))),
        lt = (a, b) -> isdominated(a, b, normal = true)
    )
    frontier = map(prgm->transform_reformat(prgm), frontier)
    return frontier
end

if Base.VERSION >= v"1.4.2"
    #snoop()
end

end
