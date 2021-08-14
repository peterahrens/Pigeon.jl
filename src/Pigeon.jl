module Pigeon

using Lerche
using SymbolicUtils
using SymbolicUtils: arguments, operation, istree
using SymbolicUtils: Fixpoint, Chain, Postwalk

export @is_str, @ie_str
export @xrule, @xarule, @xacrule

export ConcreteNode, ConcreteStatement, ConcreteExpression
export Forall, Assign, Where
export Access, Call, Literal
export Index, Workspace, Tensor, Operator
export postorder, determify, termify

include("concrete.jl")
include("parse.jl")

end