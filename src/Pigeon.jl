module Pigeon

using SymbolicUtils
using TermInterface
using TermInterface: arguments, operation, istree, similarterm
using SymbolicUtils: Fixpoint, Chain, Postwalk, Prewalk, PassThrough
using SymbolicUtils: @rule, @capture

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

export Dense, Fiber, coiter, locate

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
include("transform_normalize.jl")
include("transform_ssa.jl")
include("dimensionalize.jl")
include("lower_asymptote.jl")
include("containment.jl")

function snoop()
    saturate_index(@i @loop i j k A[i] += B[j] * C[j] * D[k] * E[k])
    saturate_index(@i @loop i j k A[i, j] = B[i, k] * C[k, j] * x[j])
    saturate_index(@i @loop i j A[i] = (-B[j]) * C[j] + D[k])
end

macro name(args::Symbol...)
    return Expr(:block, map(arg->:($(esc(arg)) = Name($(QuoteNode(arg)))), args)..., :(($(map(esc, args)...), )))
end

if Base.VERSION >= v"1.4.2"
    #snoop()
end
end