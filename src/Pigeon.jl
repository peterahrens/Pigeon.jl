module Pigeon

using SymbolicUtils
using SymbolicUtils: arguments, operation, istree, similarterm
using SymbolicUtils: Fixpoint, Chain, Postwalk, Prewalk, PassThrough
using SymbolicUtils: @rule

using Base.Iterators: product
using Combinatorics


export @i_str
export @capture

export IndexNode, IndexStatement, IndexExpression
export Loop, Assign, With, Access, Call
export loop, assign, with, access, call
export Pass, Literal, Workspace, Name
export postorder, value, name

export saturate_index
export normalize_index

include("utils.jl")
include("index.jl")
include("parse_index.jl")
include("asymptote.jl")

include("style.jl")
include("asymptotic_analysis.jl")
include("saturate.jl")
include("normalize.jl")
include("containment.jl")

function snoop()
    saturate_index(i"∀ i, j, k A[i] += B[j] * C[j] * D[k] * E[k]")
    saturate_index(i"∀ i, j, k A[i, j] = B[i, k] * C[k, j] * x[j]")
    saturate_index(i"∀ i, j A[i] = (-B[j]) * C[j] + D[k]")

    i"f(B[i, k] * C[k, j]^3, 42)"

    i"""
        ∀ i (
            ∀ j A[i, j] += w[j]
        with
            ∀ j, k w[j] += B[i, k] * C[k, j]
        )
    """
end

macro name(args::Symbol...)
    return Expr(:block, map(arg->:($(esc(arg)) = Name($(QuoteNode(arg)))), args)..., :(($(map(esc, args)...), )))
end

if Base.VERSION >= v"1.4.2"
    #snoop()
end
end