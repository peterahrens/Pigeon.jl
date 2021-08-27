abstract type ConcreteNode end
abstract type ConcreteStatement <: ConcreteNode end
abstract type ConcreteExpression <: ConcreteNode end
abstract type ConcreteTerminal <: ConcreteExpression end

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
        print(io, ")")
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
Base.hash(a::ConcreteNode, h::UInt) = hash(operation(a), hash(arguments(a), h))

#=
function Base.:(==)(a::T, b::T) where {T <: ConcreteNode}
    if istree(a) && istree(b)
        (operation(a) == operation(b)) && 
        (arguments(a) == arguments(b))
    else
        invoke(==, Tuple{Any, Any}, a, b)
    end
end
=#

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

struct Pass <: ConcreteStatement end

SymbolicUtils.istree(stmt::Pass) = false

show_statement(io, mime, stmt::Pass, level) = print(io, tab^level * "()")

struct Workspace <: ConcreteTerminal
    n
end

SymbolicUtils.istree(ex::Workspace) = false
Base.hash(ex::Workspace, h::UInt) = hash((Workspace, ex.n), h)

function show_expression(io, ex::Workspace)
    print(io, "{")
    show_expression(io, mime, ex.n)
    print(io, "}[...]")
end

struct Name <: ConcreteTerminal
    name
end

SymbolicUtils.istree(ex::Name) = false
Base.hash(ex::Name, h::UInt) = hash((Name, ex.name), h)

show_expression(io, mime, ex::Name) = print(io, ex.name)

name(ex::Name) = ex.name

struct Literal <: ConcreteTerminal
    val
end

value(ex::Literal) = ex.val

SymbolicUtils.istree(ex::Literal) = false
Base.hash(ex::Literal, h::UInt) = hash((Literal, ex.val), h)

show_expression(io, mime, ex::Literal) = print(io, ex.val)

struct Where <: ConcreteStatement
	cons::Any
	prod::Any
end
Base.:(==)(a::Where, b::Where) = a.cons == b.cons && a.prod == b.prod

_where(args...) = _where!(vcat(args...))
_where!(args) = Where(args[1], args[2])

SymbolicUtils.istree(stmt::Where) = true
SymbolicUtils.operation(stmt::Where) = _where
SymbolicUtils.arguments(stmt::Where) = Any[stmt.cons, stmt.prod]
SymbolicUtils.similarterm(::ConcreteNode, ::typeof(_where), args, T...) = _where!(args)

function show_statement(io, mime, stmt::Where, level)
    print(io, tab^level * "(\n")
    show_statement(io, mime, stmt.cons, level + 1)
    print(io, "\n" * tab^level * "where\n")
    show_statement(io, mime, stmt.prod, level + 1)
    print(io, tab^level * ")\n")
end

struct Loop <: ConcreteStatement
	idxs::Vector{Any}
	body::Any
end
Base.:(==)(a::Loop, b::Loop) = a.idxs == b.idxs && a.body == b.body

loop(args...) = loop!(vcat(args...))
loop!(args) = Loop(args, pop!(args))

SymbolicUtils.istree(stmt::Loop) = true
SymbolicUtils.operation(stmt::Loop) = loop
SymbolicUtils.arguments(stmt::Loop) = Any[stmt.idxs; stmt.body]
SymbolicUtils.similarterm(::ConcreteNode, ::typeof(loop), args, T...) = loop!(args)

function show_statement(io, mime, stmt::Loop, level)
    print(io, tab^level * "∀ ")
    if !isempty(stmt.idxs)
        show_expression(io, mime, stmt.idxs[1])
        for idx in stmt.idxs[2:end]
            print(io,", ")
            show_expression(io, mime, idx)
        end
    end
    print(io," \n")
    show_statement(io, mime, stmt.body, level + 1)
end

struct Assign <: ConcreteStatement
	lhs::Any
	op::Any
	rhs::Any
end
Base.:(==)(a::Assign, b::Assign) = a.lhs == b.lhs && a.op == b.op && a.rhs == b.rhs

assign(args...) = assign!(vcat(args...))
function assign!(args)
    if length(args) == 2
        Assign(args[1], nothing, args[2])
    elseif length(args) == 3
        Assign(args[1], args[2], args[3])
    else
        throw(ArgumentError("wrong number of arguments to assign"))
    end
end

SymbolicUtils.istree(stmt::Assign) = true
SymbolicUtils.operation(stmt::Assign) = assign
function SymbolicUtils.arguments(stmt::Assign)
    if stmt.op === nothing
        Any[stmt.lhs, stmt.rhs]
    else
        Any[stmt.lhs, stmt.op, stmt.rhs]
    end
end
SymbolicUtils.similarterm(::ConcreteNode, ::typeof(assign), args, T...) = assign!(args)

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

struct Call <: ConcreteExpression
    op::Any
    args::Vector{Any}
end
Base.:(==)(a::Call, b::Call) = a.op == b.op && a.args == b.args

call(args...) = call!(vcat(args...))
call!(args) = Call(popfirst!(args), args)

SymbolicUtils.istree(ex::Call) = true
SymbolicUtils.operation(ex::Call) = call
SymbolicUtils.arguments(ex::Call) = Any[ex.op; ex.args]
SymbolicUtils.similarterm(::ConcreteNode, ::typeof(call), args, T...) = call!(args)

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

struct Access <: ConcreteExpression
    tns::Any
    idxs::Vector{Any}
end
Base.:(==)(a::Access, b::Access) = a.tns == b.tns && a.idxs == b.idxs

access(args...) = access!(vcat(args...))
access!(args) = Access(popfirst!(args), args)

SymbolicUtils.istree(ex::Access) = true
SymbolicUtils.operation(ex::Access) = access
SymbolicUtils.arguments(ex::Access) = Any[ex.tns; ex.idxs]
SymbolicUtils.similarterm(::ConcreteNode, ::typeof(access), args, T...) = access!(args)

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