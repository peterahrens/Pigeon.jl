abstract type ConcreteNode end
abstract type ConcreteStatement <: ConcreteNode end
abstract type ConcreteExpression <: ConcreteNode end

const tab = "  "

function Base.show(io::IO, stmt::ConcreteStatement)
	print(io, "\"\"\"\n")
	show_statement(io, stmt, 0)
	print(io, "\"\"\"\n")
end

function Base.show(io::IO, ex::ConcreteExpression)
	print(io, "\"")
	show_expression(io, ex)
	print(io, "\"")
end

function postorder(f, node::ConcreteNode)
    if istree(node)
        f(operation(node)(map(child->postorder(f, child), arguments(node))...))
    else
        f(node)
    end
end
function postorder(f, node::SymbolicUtils.Term)
    f(term(operation(node), map(child->postorder(f, child), arguments(node))...))
end
Base.map(f, node::ConcreteNode) = postorder(f, node)

termify(node::SymbolicUtils.Term) = node
function termify(node::ConcreteNode)
    if istree(node)
        return term(operation(node), map(termify, arguments(node))...)
    else
        return node
    end
end

determify(node) = node
determify(node::SymbolicUtils.Term) = operation(node)(map(determify, arguments(node))...)

struct Body
    stmt
end

SymbolicUtils.istree(stmt::Body) = true
SymbolicUtils.operation(stmt::Body) = Body
SymbolicUtils.arguments(stmt::Body) = [stmt.stmt]

struct Forall <: ConcreteStatement
	idxs
	body

    Forall(args...) = new(args[1:end-1], args[end])
    #function Forall(args...)
    #    i = findfirst(arg->(arg isa Body), args)
    #    @assert i !== nothing && findnext(arg->(arg isa Body), args, i + 1) === nothing
    #    new([args[j] for j in eachindex(args) if i != j], args[i])
    #end
end

SymbolicUtils.istree(stmt::Forall) = true
SymbolicUtils.operation(stmt::Forall) = Forall
SymbolicUtils.arguments(stmt::Forall) = [stmt.idxs..., stmt.body]

function show_statement(io, stmt::Forall, level)
    print(io, tab^level * "∀ ")
    show_expression(io, stmt.idx)
    print(io," \n")
    show_statement(io, stmt.body, level + 1)
end

struct Workspace <: ConcreteExpression
    n
end

SymbolicUtils.istree(ex::Workspace) = false

function show_expression(io, ex::Workspace)
    print(io, "{")
    show_expression(io, ex.n)
    print(io, "}[...]")
end

struct Name <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Name) = false

show_expression(io, ex::Name) = print(io, ex.name)

struct Literal <: ConcreteExpression
    val
end

SymbolicUtils.istree(ex::Literal) = false

show_expression(io, ex::Literal) = print(io, ex.val)

struct Index <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Index) = true
SymbolicUtils.operation(ex::Index) = Index
SymbolicUtils.arguments(ex::Index) = [ex.name]

show_expression(io, ex::Index) = show_expression(io, ex.name)

struct Where <: ConcreteStatement
	cons
	prod
end

SymbolicUtils.istree(stmt::Where) = true
SymbolicUtils.operation(stmt::Where) = Where
SymbolicUtils.arguments(stmt::Where) = [stmt.cons, stmt.prod]

function show_statement(io, stmt::Where, level)
    print(io, tab^level * "(\n")
    show_statement(io, stmt.cons, level + 1)
    print(io, "\n" * tab^level * "where\n")
    show_statement(io, stmt.prod, level + 1)
    print(io, tab^level * ")\n")
end

struct Assign <: ConcreteStatement
	lhs
	op
	rhs
    Assign(lhs, op, rhs) = new(lhs, op, rhs)
    Assign(lhs, rhs) = new(lhs, nothing, rhs)
end

SymbolicUtils.istree(stmt::Assign) = true
SymbolicUtils.operation(stmt::Assign) = Assign
function SymbolicUtils.arguments(stmt::Assign)
    if stmt.op === nothing
        [stmt.lhs, stmt.rhs]
    else
        [stmt.lhs, stmt.op, stmt.rhs]
    end
end

function show_statement(io, stmt::Assign, level)
    print(io, tab^level)
    show_expression(io, stmt.lhs)
    print(io, " ")
    if stmt.op !== nothing
        show_expression(io, stmt.op)
    end
    print(io, "= ")
    show_expression(io, stmt.rhs)
    print(io, "\n")
end

struct Operator <: ConcreteExpression
    val
end

SymbolicUtils.istree(ex::Operator) = true
SymbolicUtils.operation(ex::Operator) = Operator
SymbolicUtils.arguments(ex::Operator) = [ex.val]

show_expression(io, ex::Operator) = show_expression(io, ex.val)

struct Call <: ConcreteExpression
    op
    args
    Call(op, args...) = new(op, args)
    #function Call(args...)
    #    i = findfirst(arg->(arg isa Operator), args)
    #    @assert i !== nothing && findnext(arg->(arg isa Operator), args, i + 1) === nothing
    #    new(args[i], [args[j] for j in eachindex(args) if i != j])
    #end
end

(op::Operator)(args...) = Call(op, args...)

SymbolicUtils.istree(ex::Call) = true
SymbolicUtils.operation(ex::Call) = Call
SymbolicUtils.arguments(ex::Call) = [ex.op, ex.args...]

function show_expression(io, ex::Call)
    show_expression(io, ex.op)
    print(io, "(")
    for arg in ex.args[1:end-1]
        show_expression(io, arg)
        print(io, ", ")
    end
    show_expression(io, ex.args[end])
    print(io, ")")
end

struct Tensor <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Tensor) = true
SymbolicUtils.operation(ex::Tensor) = Tensor
SymbolicUtils.arguments(ex::Tensor) = [ex.name]

show_expression(io, ex::Tensor) = show_expression(io, ex.name)

struct Access <: ConcreteExpression
    tns
    idxs
    Access(tns, inds...) = new(tns, inds)
    #function Access(args...)
    #    i = findfirst(arg->(arg isa Tensor), args)
    #    @assert i !== nothing && findnext(arg->(arg isa Tensor), args, i+1) === nothing
    #    new(args[i], [args[j] for j in eachindex(args) if i != j])
    #end
end

SymbolicUtils.istree(ex::Access) = true
SymbolicUtils.operation(ex::Access) = Access
SymbolicUtils.arguments(ex::Access) = [ex.tns, ex.idxs...]

function show_expression(io, ex::Access)
    show_expression(io, ex.tns)
    print(io, "[")
    if length(ex.idxs) >= 1
        for idx in ex.idxs[1:end-1]
            show_expression(io, idx)
            print(io, ", ")
        end
        show_expression(io, ex.idxs[end])
    end
    print(io, "]")
end

show_expression(io, ex) = print(io, ex)