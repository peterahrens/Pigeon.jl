#TODO this assumes arguments are unique
function enumerate_schedules_old(stmt)
	normalize = Fixpoint(Postwalk(Chain([
	    (@ex@rule i"+(~a, ~b, ~c, ~~d)" => i"~a + +(~b, ~c, ~~d)"),
	    (@ex@rule i"+(~a)" => ~a),
	    (@ex@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@ex@rule i"- (- ~a)" => ~a),
	    (@ex@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@ex@rule i"*(~a, ~b, ~c, ~~d)" => i"~a * *(~b, ~c, ~~d)"),
	    (@ex@rule i"*(~a)" => ~a),
	    (@ex@rule i"∀ ~i, ~j, ~~k ~s" => i"∀ ~i ∀ ~j, ~~k ~s"),
	    (@ex@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    #(@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
	    #(@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)
	])))
	stmt = normalize(stmt)
	universe = Set()
	postorder(node->(push!(universe, node); node), stmt)
    
	function step(node)
	    if istree(node)
		stepped = false
		args′ = map(arguments(node)) do arg
		    if !stepped
			(stepped′, arg′) = step(arg)
			stepped |= stepped′
			return arg′
		    else
			return arg
		    end
		end
		if stepped
		    node′ = normalize(operation(node)(args′))
		    push!(universe, node′)
		    return (true, node′)
		end
	    end
	    for transform in [
		(@ex@rule i"~a + (~b + ~c)" => i"(~a + ~b) + ~c"),
		(@ex@rule i"(~a + ~b) + ~c" => i"~a + (~b + ~c)"),
		(@ex@rule i"~a + ~b" => i"~b + ~a"),
		(@ex@rule i"~a * (~b * ~c)" => i"(~a * ~b) * ~c"),
		(@ex@rule i"(~a * ~b) * ~c" => i"~a * (~b * ~c)"),
		(@ex@rule i"~a * ~b" => i"~b * ~a"),
		(@ex@rule i"∀ ~i ∀ ~j ~s" => i"∀ ~j ∀ ~i ~s"),
		(@ex@rule i"~Ai ~~f= ~g(~a, ~h(~~b))" =>
		    w₊(i"~Ai ~~f= ~g(~a, $w₀) with $w₀ = ~h(~~b)")),
		(@ex@rule i"~Ai += +(~a, ~f(~~b))" =>
		    w₊(i"~Ai += +(~a, $w₀) with $w₀ += ~f(~~b)")),
		(@ex@rule i"~Ai += *(~a, ~f(~~b))" =>
		    w₊(i"~Ai += *(~a, $w₀) with $w₀ += ~f(~~b)")),
		(@ex@rule i"∀ ~i (~c with ~p)" => if (~i in indices(~c)) && !(~i in indices(~p))
		    i"(∀ ~i ~c) with ~p" end),
		(@ex@rule i"∀ ~i (~c with ~p)" => if (~i in indices(~c)) && (~i in indices(~p))
		    i"(∀ ~i ~c) with (∀ ~i ~p)" end),
		(@ex@rule i"∀ ~i (~Ai += ~b * $w₁ with ~p)" => if !(~i in indices(i"~Ai += ~b * $w₁")) && (~i in indices(~p))
		    i"~Ai += ~b * $w₁ with (∀ ~i ~p)" end),
	    ]
		node′ = transform(node)
		if node′ !== nothing && !(node′ in universe)
		    postorder(subnode -> (push!(universe, subnode); subnode), node′)
		    return (true, node′)
		end
	    end
	    return (false, node)
	end
    
	frontier = Any[stmt]
	result = Any[stmt]
    
	simplify = Fixpoint(Postwalk(Chain([
	    (@ex@rule i"+(~~a, +(~~b), ~~c)" => i"+(~~a, ~~b, ~~c)"),
	    (@ex@rule i"+(~a)" => ~a),
	    (@ex@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@ex@rule i"- (- ~a)" => ~a),
	    (@ex@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@ex@rule i"*(~~a, *(~~b), ~~c)" => i"*(~~a, ~~b, ~~c)"),
	    (@ex@rule i"*(~a)" => ~a),
	    (@ex@rule i"∀ ~~i ∀ ~~j ~s" => i"∀ ~~i, ~~j ~s"),
	    (@ex@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    (@ex@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end),
	    (@ex@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end),
	])))
    
	while !isempty(frontier)
	    stmt = pop!(frontier)
    
	    while true
		(stepped, stmt′) = step(stmt)
		if stepped
		    push!(frontier, stmt′)
		    push!(result, name_workspaces(stmt′))
		else
		    break
		end
	    end
	end
	return unique(map(simplify, result))
    end 
 
    #=
struct Initial <: IndexStatement
	op::Any
	val::Any
end
Base.:(==)(a::Initial, b::Initial) = a.op == b.op && a.val == b.val

initial(args...) = initial!(vcat(args...))
function initial!(args)
    @assert length(args) == 2
    return Initial(args[1], args[2])
end

SymbolicUtils.istree(ex::Initial) = true
SymbolicUtils.operation(ex::Initial) = initial
SymbolicUtils.arguments(ex::Initial) = [ex.op, ex.val]
SymbolicUtils.similarterm(::IndexNode, ::typeof(initial), args, T...) = initial!(args)

function show_expression(io, mime, ex::Initial, level)
    show_expression(io, mime, ex.lhs)
    print(io, "(")
    print(io, ex.op)
    print(io, ", ")
    print(io, ex.val)
    print(io, ")")
end
=#