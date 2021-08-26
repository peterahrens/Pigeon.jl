module Pigeon

using Lerche
using SymbolicUtils
using SymbolicUtils: arguments, operation, istree
using SymbolicUtils: Fixpoint, Chain, Postwalk

export @i_str
export @capture

export ConcreteNode, ConcreteStatement, ConcreteExpression
export Loop, Assign, Where, Access, Call
export loop, assign, _where, access, call
export Pass, Literal, Workspace, Name
export postorder, value, name

include("utils.jl")
include("concrete.jl")
include("parse.jl")


#=
is"""
    ∀ i (
        ∀ j A[i, j] += w[j]
    where
        ∀ j, k w[j] += B[i, k] * C[k, j]
    )
"""
=#

end