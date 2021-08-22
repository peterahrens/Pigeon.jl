abstract type ConcreteNode end
abstract type ConcreteStatement <: ConcreteNode end
abstract type ConcreteExpression <: ConcreteNode end

const tab = "  "

function Base.show(io::IO, mime::MIME"text/plain", stmt::ConcreteStatement)
	println(io, "\"\"\"")
	show_statement(io, mime, stmt, 0)
	println(io, "\"\"\"")
end

function Base.show(io::IO, mime::MIME"text/plain", ex::ConcreteExpression)
	print(io, "\"")
	show_expression(io, mime, ex)
	print(io, "\"")
end

function Base.show(io::IO, ex::ConcreteNode)
    if istree(ex)
        print(io, operation(ex))
        print(io, "(")
        for arg in arguments(ex)[1:end-1]
            show(io, arg)
            print(io, ", ")
        end
        if length(arguments(ex)) >= 1
            show(io, last(arguments(ex)))
        end
    else
        invoke(show, Tuple{IO, Any}, io, ex)
    end
end

function postorder(f, node::ConcreteNode)
    if istree(node)
        f(operation(node)(map(child->postorder(f, child), arguments(node))...))
    else
        f(node)
    end
end

Base.isless(a::ConcreteNode, b::ConcreteNode) = hash(a) < hash(b)
Base.hash(a::ConcreteNode, h::UInt) = hash((operation(a), arguments(a)...), h)

function postorder(f, node::SymbolicUtils.Term)
    f(term(operation(node), map(child->postorder(f, child), arguments(node))...))
end
Base.map(f, node::ConcreteNode) = postorder(f, node)

#termify(node::SymbolicUtils.Term) = node
#function termify(node::ConcreteNode)
#    if istree(node)
#        return term(operation(node), map(termify, arguments(node))...)
#    else
#        return node
#    end
#end
#
#determify(node) = node
#determify(node::SymbolicUtils.Term) = operation(node)(map(determify, arguments(node))...)

struct Body <: ConcreteStatement
    stmt
end

SymbolicUtils.istree(stmt::Body) = true
SymbolicUtils.operation(stmt::Body) = Body
SymbolicUtils.arguments(stmt::Body) = [stmt.stmt]

show_statement(io, mime, stmt::Body, level) = show_statement(io, mime, stmt.stmt, level)

struct Pass <: ConcreteStatement end

SymbolicUtils.istree(stmt::Pass) = false

show_statement(io, mime, stmt::Pass, level) = print(io, tab^level * "()")

struct Loop <: ConcreteStatement
	idxs
	body

    Loop(args...) = new(args[1:end-1], args[end])
    #function Loop(args...)
    #    i = findfirst(arg->(arg isa Body), args)
    #    @assert i !== nothing && findnext(arg->(arg isa Body), args, i + 1) === nothing
    #    new([args[j] for j in eachindex(args) if i != j], args[i])
    #end
end

SymbolicUtils.istree(stmt::Loop) = true
SymbolicUtils.operation(stmt::Loop) = Loop
SymbolicUtils.arguments(stmt::Loop) = [stmt.idxs..., stmt.body]

function show_statement(io, mime, stmt::Loop, level)
    print(io, tab^level * "∀ ")
    show_expression(io, mime, stmt.idxs[1])
    for idx in stmt.idxs[2:end]
        print(io,", ")
        show_expression(io, mime, idx)
    end
    print(io," \n")
    show_statement(io, mime, stmt.body, level + 1)
end

struct Workspace <: ConcreteExpression
    n
end

SymbolicUtils.istree(ex::Workspace) = false
Base.hash(ex::Workspace, h::UInt) = hash((Workspace, ex.n), h)

function show_expression(io, ex::Workspace)
    print(io, "{")
    show_expression(io, mime, ex.n)
    print(io, "}[...]")
end

struct Name <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Name) = false
Base.hash(ex::Name, h::UInt) = hash((Name, ex.name), h)

show_expression(io, mime, ex::Name) = print(io, ex.name)

struct Literal <: ConcreteExpression
    val
end

value(ex::Literal) = ex.val

SymbolicUtils.istree(ex::Literal) = false
Base.hash(ex::Literal, h::UInt) = hash((Literal, ex.val), h)

show_expression(io, mime, ex::Literal) = print(io, ex.val)

struct Index <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Index) = true
SymbolicUtils.operation(ex::Index) = Index
SymbolicUtils.arguments(ex::Index) = [ex.name]

show_expression(io, mime, ex::Index) = show_expression(io, mime, ex.name)

struct Quantified <: ConcreteExpression
    idx 
end

SymbolicUtils.istree(ex::Quantified) = true
SymbolicUtils.operation(ex::Quantified) = Quantified
SymbolicUtils.arguments(ex::Quantified) = [ex.idx]

show_expression(io, mime, ex::Quantified) = show_expression(io, mime, ex.idx)

struct Where <: ConcreteStatement
	cons
	prod
end

SymbolicUtils.istree(stmt::Where) = true
SymbolicUtils.operation(stmt::Where) = Where
SymbolicUtils.arguments(stmt::Where) = [stmt.cons, stmt.prod]

function show_statement(io, mime, stmt::Where, level)
    print(io, tab^level * "(\n")
    show_statement(io, mime, stmt.cons, level + 1)
    print(io, "\n" * tab^level * "where\n")
    show_statement(io, mime, stmt.prod, level + 1)
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

function show_statement(io, mime, stmt::Assign, level)
    print(io, tab^level)
    show_expression(io, mime, stmt.lhs)
    print(io, " ")
    if stmt.op !== nothing
        show_expression(io, mime, stmt.op)
    end
    print(io, "= ")
    show_expression(io, mime, stmt.rhs)
    print(io, "\n")
end

struct Operator <: ConcreteExpression
    val
end

SymbolicUtils.istree(ex::Operator) = true
SymbolicUtils.operation(ex::Operator) = Operator
SymbolicUtils.arguments(ex::Operator) = [ex.val]

show_expression(io, mime, ex::Operator) = show_expression(io, mime, ex.val)

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

function show_expression(io, mime, ex::Call)
    show_expression(io, mime, ex.op)
    print(io, "(")
    for arg in ex.args[1:end-1]
        show_expression(io, mime, arg)
        print(io, ", ")
    end
    show_expression(io, mime, ex.args[end])
    print(io, ")")
end

struct Tensor <: ConcreteExpression
    name
end

SymbolicUtils.istree(ex::Tensor) = true
SymbolicUtils.operation(ex::Tensor) = Tensor
SymbolicUtils.arguments(ex::Tensor) = [ex.name]

show_expression(io, mime, ex::Tensor) = show_expression(io, mime, ex.name)

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

function show_expression(io, mime, ex::Access)
    show_expression(io, mime, ex.tns)
    print(io, "[")
    if length(ex.idxs) >= 1
        for idx in ex.idxs[1:end-1]
            show_expression(io, mime, idx)
            print(io, ", ")
        end
        show_expression(io, mime, ex.idxs[end])
    end
    print(io, "]")
end

show_expression(io, mime, ex) = print(io, ex)