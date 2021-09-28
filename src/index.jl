abstract type IndexNode end
abstract type IndexStatement <: IndexNode end
abstract type IndexExpression <: IndexNode end
abstract type IndexTerminal <: IndexExpression end

const tab = "  "

function Base.show(io::IO, mime::MIME"text/plain", stmt::IndexStatement)
	println(io, "\"\"\"")
	show_statement(io, mime, stmt, 0)
	println(io, "\"\"\"")
end

function Base.show(io::IO, mime::MIME"text/plain", ex::IndexExpression)
	print(io, "\"")
	show_expression(io, mime, ex)
	print(io, "\"")
end

function Base.show(io::IO, ex::IndexNode)
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

function postorder(f, node::IndexNode)
    if istree(node)
        f(operation(node)(map(child->postorder(f, child), arguments(node))...))
    else
        f(node)
    end
end

Base.isless(a::IndexNode, b::IndexNode) = hash(a) < hash(b)
function Base.hash(a::IndexNode, h::UInt)
    if istree(a)
        hash(operation(a), hash(arguments(a), h))
    else
        invoke(hash, Tuple{Any, UInt}, a, h)
    end
end

#=
function Base.:(==)(a::T, b::T) with {T <: IndexNode}
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
Base.map(f, node::IndexNode) = postorder(f, node)

struct Literal <: IndexTerminal
    val
end

value(ex) = ex
value(ex::Literal) = ex.val
isliteral(ex::Literal) = true
isliteral(ex) = true
isliteral(ex::IndexNode) = false

TermInterface.istree(::Type{<:Literal}) = false
Base.hash(ex::Literal, h::UInt) = hash((Literal, ex.val), h)

show_expression(io, mime, ex::Literal) = print(io, ex.val)

struct Pass <: IndexStatement
	tns::Any
end
Base.:(==)(a::Pass, b::Pass) = a.tns == b.tns

pass(args...) = pass!(vcat(args...))
pass!(args) = Pass(args[1])

TermInterface.istree(::Type{<:Pass}) = true
TermInterface.operation(stmt::Pass) = pass
TermInterface.arguments(stmt::Pass) = Any[stmt.tns]
TermInterface.similarterm(::IndexNode, ::typeof(pass), args, T...) = pass!(args)

function show_statement(io, mime, stmt::Pass, level)
    print(io, tab^level * "(")
    show_expression(io, mime, stmt.tns)
    print(io, ")")
end

struct Workspace <: IndexTerminal
    n
end

TermInterface.istree(::Type{<:Workspace}) = false
Base.hash(ex::Workspace, h::UInt) = hash((Workspace, ex.n), h)

function show_expression(io, ex::Workspace)
    print(io, "{")
    show_expression(io, mime, ex.n)
    print(io, "}[...]")
end


struct Name <: IndexTerminal
    name
end

TermInterface.istree(::Type{<:Name}) = false
Base.hash(ex::Name, h::UInt) = hash((Name, ex.name), h)

show_expression(io, mime, ex::Name) = print(io, ex.name)

getname(ex::Name) = ex.name
rename(ex::Name, name) = Name(name)

struct With <: IndexStatement
	cons::Any
	prod::Any
end
Base.:(==)(a::With, b::With) = a.cons == b.cons && a.prod == b.prod

with(args...) = with!(vcat(args...))
with!(args) = With(args[1], args[2])

TermInterface.istree(::Type{<:With}) = true
TermInterface.operation(stmt::With) = with
TermInterface.arguments(stmt::With) = Any[stmt.cons, stmt.prod]
TermInterface.similarterm(::IndexNode, ::typeof(with), args, T...) = with!(args)

function show_statement(io, mime, stmt::With, level)
    print(io, tab^level * "(\n")
    show_statement(io, mime, stmt.cons, level + 1)
    print(io, "\n" * tab^level * "with\n")
    show_statement(io, mime, stmt.prod, level + 1)
    print(io, tab^level * ")\n")
end

struct Loop <: IndexStatement
	idxs::Vector{Any}
	body::Any
end
Base.:(==)(a::Loop, b::Loop) = a.idxs == b.idxs && a.body == b.body

loop(args...) = loop!(vcat(args...))
loop!(args) = Loop(args, pop!(args))

TermInterface.istree(::Type{<:Loop}) = true
TermInterface.operation(stmt::Loop) = loop
TermInterface.arguments(stmt::Loop) = Any[stmt.idxs; stmt.body]
TermInterface.similarterm(::IndexNode, ::typeof(loop), args, T...) = loop!(args)

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

struct Assign{Lhs} <: IndexStatement
	lhs::Lhs
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

TermInterface.istree(::Type{<:Assign})= true
TermInterface.operation(stmt::Assign) = assign
function TermInterface.arguments(stmt::Assign)
    if stmt.op === nothing
        Any[stmt.lhs, stmt.rhs]
    else
        Any[stmt.lhs, stmt.op, stmt.rhs]
    end
end
TermInterface.similarterm(::IndexNode, ::typeof(assign), args, T...) = assign!(args)

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

struct Call <: IndexExpression
    op::Any
    args::Vector{Any}
end
Base.:(==)(a::Call, b::Call) = a.op == b.op && a.args == b.args

call(args...) = call!(vcat(args...))
call!(args) = Call(popfirst!(args), args)

TermInterface.istree(::Type{<:Call}) = true
TermInterface.operation(ex::Call) = call
TermInterface.arguments(ex::Call) = Any[ex.op; ex.args]
TermInterface.similarterm(::IndexNode, ::typeof(call), args, T...) = call!(args)

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

struct Read <: IndexTerminal end
struct Write <: IndexTerminal end
struct Update <: IndexTerminal end

struct Access{T, M} <: IndexExpression
    tns::T
    mode::M
    idxs::Vector
end
Base.:(==)(a::Access, b::Access) = a.tns == b.tns && a.idxs == b.idxs

access(args...) = access!(vcat(Any[], args...))
access!(args) = Access(popfirst!(args), popfirst!(args), args)

TermInterface.istree(::Type{<:Access}) = true
TermInterface.operation(ex::Access) = access
TermInterface.arguments(ex::Access) = Any[ex.tns; ex.mode; ex.idxs]
TermInterface.similarterm(::IndexNode, ::typeof(access), args, T...) = access!(args)

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


getresult(stmt::Assign) = getresult(stmt.lhs)
getresult(stmt::Access) = getresult(stmt.tns)
getresult(stmt::Loop) = getresult(stmt.body)
getresult(stmt::With) = getresult(stmt.cons)
getresult(stmt::Pass) = getresult(stmt.tns)
getresult(arg) = arg
