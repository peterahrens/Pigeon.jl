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

# What to change?
#
# (A) We want to make the coiterate_case function able to dispatch access handling based on tensors
# options:
#   1. rewrite rule dispatch (do a pass to collect rules, match in context you want, check concrete types)
#      pros: 
#           can express a wide variety of patterns, including the one we want
#           we probably need to use some version of this for annihilation anyway
#      cons:
#           the common case is complicated
#           dispatch is order-dependent
#   2. type-based dispatch (type the tree)
#      Pros:
#           expressing the dispatch we want is a one-liner
#      Cons:
#           There's nothing to enforce that dispatch can become ambiguous
#   3. delay matching (tensor declares result that gets unpacked into access later)
#   3 (continued). give a list of parents to the visitor function
#       Pros:
#           Dispatch is a one-liner
#       Cons:
#           delays are confusing to implement
#   4. make tensors responsible for holding indices
#       Pros:
#           Dispatch is super clear and straightforward
#           Makes some semantic sense
#       Cons:
#           There's no good interface for if indices are shifted or something (in dense case)
#           Tensors need to implement more complicated functions
#   5. use special Access types
#       Pros:
#           Dispatch is super clear and straightforward
#           No ambiguities because Accesses and References are typed by their tensor
#           Common case is easy
#           This is sortof like 4, with nice defaults. I'm choosing 4. We might do the same thing for accesses.
#       Cons:
#           Doesn't solve more complicated dispatch problems (How to dispatch access lowering? probably style resolution let's be honest)
#           Sortof confusing because every implementation needs to do the same boilerplate to lower indices (is there any solution that avoids this?)
#   6. use style resolution at every level
#       Pros:
#           consistent
#       Cons:
#           messy
#           sorta makes most sense for forall, where, and assign statements, not access statements, which usually feel very terminal
#   7. need to differentiate lhs from rhs access
#       Could use "reference" type, could pass in a "write" parameter in traversals, some context-based approaches help too.
#       I like the "reference" type because it's clean, but it's unclear if Access{Any} is more specific than Union{Access{T}, Reference{T}}
#       What if we pass in a write or read parameter into the Access?
#       Access{Tns, true} vs Access{Tns, false} ?
#   Notes: What we're dealing with is that tensors belong more to the access
#   node itself than to the children of the access, and that it's more
#   convenient to treat them as terminals (indices cannot be functions). Indices
#   usually aren't functions, but if they are, we sorta have bigger problems no?
#   You won't get your Ph.D. if you handle indices that are functions.
#   Notes: styles should move through an "access style resolution" step if we are gonna make this work.
# come back to (A)
# We want to handle global iteration counting and contexts with mutability rather than functionally (cleaner)
# We want to simplify assignments to references known to be entirely implicit
# We want to initialize workspaces
# We need tests