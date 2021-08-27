module Pigeon

using Lerche
using SymbolicUtils
using SymbolicUtils: arguments, operation, istree, similarterm
using SymbolicUtils: Fixpoint, Chain, Postwalk, Prewalk, PassThrough
using SymbolicUtils: @rule

using Base.Iterators: product
using Combinatorics


export @i_str
export @capture

export IndexNode, IndexStatement, IndexExpression
export Loop, Assign, Where, Access, Call
export loop, assign, _where, access, call
export Pass, Literal, Workspace, Name
export postorder, value, name

export saturate_index

include("utils.jl")
include("index.jl")
include("parse.jl")
include("saturate.jl")

function snoop()
    @time saturate_index(i"∀ i, j, k A[i] += B[j] * C[j] * D[k] * E[k]")
    @time saturate_index(i"∀ i, j, k A[i] += B[j] * C[j] * D[k] * E[k]")
    saturate_index(i"∀ i, j, k A[i, j] = B[i, k] * C[k, j] * x[j]")
    saturate_index(i"∀ i, j A[i] = (-B[j]) * C[j] + D[k]")

    i"f(B[i, k] * C[k, j]^3, 42)"

    i"""
        ∀ i (
            ∀ j A[i, j] += w[j]
        where
            ∀ j, k w[j] += B[i, k] * C[k, j]
        )
    """
end

if Base.VERSION >= v"1.4.2"
    snoop()
end
end