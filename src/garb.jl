#TODO this assumes arguments are unique
function enumerate_schedules_old(stmt)
	normalize = Fixpoint(Postwalk(Chain([
	    (@expand@rule i"+(~a, ~b, ~c, ~~d)" => i"~a + +(~b, ~c, ~~d)"),
	    (@expand@rule i"+(~a)" => ~a),
	    (@expand@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@expand@rule i"- (- ~a)" => ~a),
	    (@expand@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@expand@rule i"*(~a, ~b, ~c, ~~d)" => i"~a * *(~b, ~c, ~~d)"),
	    (@expand@rule i"*(~a)" => ~a),
	    (@expand@rule i"∀ ~i, ~j, ~~k ~s" => i"∀ ~i ∀ ~j, ~~k ~s"),
	    (@expand@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    #(@expand@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end)
	    #(@expand@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end)
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
		(@expand@rule i"~a + (~b + ~c)" => i"(~a + ~b) + ~c"),
		(@expand@rule i"(~a + ~b) + ~c" => i"~a + (~b + ~c)"),
		(@expand@rule i"~a + ~b" => i"~b + ~a"),
		(@expand@rule i"~a * (~b * ~c)" => i"(~a * ~b) * ~c"),
		(@expand@rule i"(~a * ~b) * ~c" => i"~a * (~b * ~c)"),
		(@expand@rule i"~a * ~b" => i"~b * ~a"),
		(@expand@rule i"∀ ~i ∀ ~j ~s" => i"∀ ~j ∀ ~i ~s"),
		(@expand@rule i"~Ai ~~f= ~g(~a, ~h(~~b))" =>
		    w₊(i"~Ai ~~f= ~g(~a, $w₀) where $w₀ = ~h(~~b)")),
		(@expand@rule i"~Ai += +(~a, ~f(~~b))" =>
		    w₊(i"~Ai += +(~a, $w₀) where $w₀ += ~f(~~b)")),
		(@expand@rule i"~Ai += *(~a, ~f(~~b))" =>
		    w₊(i"~Ai += *(~a, $w₀) where $w₀ += ~f(~~b)")),
		(@expand@rule i"∀ ~i (~c where ~p)" => if (~i in indices(~c)) && !(~i in indices(~p))
		    i"(∀ ~i ~c) where ~p" end),
		(@expand@rule i"∀ ~i (~c where ~p)" => if (~i in indices(~c)) && (~i in indices(~p))
		    i"(∀ ~i ~c) where (∀ ~i ~p)" end),
		(@expand@rule i"∀ ~i (~Ai += ~b * $w₁ where ~p)" => if !(~i in indices(i"~Ai += ~b * $w₁")) && (~i in indices(~p))
		    i"~Ai += ~b * $w₁ where (∀ ~i ~p)" end),
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
	    (@expand@rule i"+(~~a, +(~~b), ~~c)" => i"+(~~a, ~~b, ~~c)"),
	    (@expand@rule i"+(~a)" => ~a),
	    (@expand@rule i"~a - ~b" => i"~a + (- ~b)"),
	    (@expand@rule i"- (- ~a)" => ~a),
	    (@expand@rule i"- +(~a, ~~b)" => i"+(- ~a, - +(~~b))"),
	    (@expand@rule i"*(~~a, *(~~b), ~~c)" => i"*(~~a, ~~b, ~~c)"),
	    (@expand@rule i"*(~a)" => ~a),
	    (@expand@rule i"∀ ~~i ∀ ~~j ~s" => i"∀ ~~i, ~~j ~s"),
	    (@expand@rule i"*(~~a, - ~b, ~~c)" => i"-(*(~~a, ~b, ~~c))"),
	    (@expand@rule i"+(~~a)" => if !issorted(~~a) i"+($(sort(~~a)))" end),
	    (@expand@rule i"*(~~a)" => if !issorted(~~a) i"*($(sort(~~a)))" end),
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
 