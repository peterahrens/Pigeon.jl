function recognize(r, s, pos)
    if (m = findnext(r, s, pos)) !== nothing && first(m) == pos
        return last(m) + 1
    end
end

function parse_julia_generous(s, pos)
    @assert pos isa Integer
    return Meta.parse(s, pos, greedy=false)
end

function parse_julia_greedy(s, pos)
	ex, pos′ = Meta.parse(s, pos, raise=false)
    if ex.head == :error && length(ex.args) == 1 &&
        (m = match(r"^extra token \\\"(.*)\\\" after end of expression", ex.args[1])) != nothing# &&
        #m.captures[1] in ["∀", "loop", "with", ")", "(", ","]
        #yeah, this substring is quadratic space
        #no, i don't care
        return Meta.parse(s[1:pos′ - lastindex(m.captures[1]) - 1], pos)
    elseif ex.head == :error && length(ex.args) == 1 &&
        (m = match(r"^space before \"\(\" not allowed in", ex.args[1])) != nothing
        return Meta.parse(s[1:pos′ - lastindex("(") - 1], pos)
    end
    return (ex, pos′)
end

function parse_index_with(s, pos)
    (prod, pos) = parse_index_loop(s, pos)
    while (pos′ = recognize(r"\s*(\bwith\b)\s*", s, pos)) !== nothing
        (cons, pos) = parse_index_loop(s, pos′)
        prod = :(with($prod, $cons))
    end
    (prod, pos)
end

function parse_index_loop(s, pos)
    if (pos′ = recognize(r"\s*(∀|(\bloop\b))\s*", s, pos)) !== nothing
        (ex, pos) = parse_julia_generous(s, pos′)
        idxs = [capture_index_expression(ex, true)]
        while (pos′ = recognize(r",\s*", s, pos)) !== nothing
            (ex, pos) = parse_julia_generous(s, pos′)
            push!(idxs, capture_index_expression(ex, true))
        end
        (body, pos) = parse_index_paren(s, pos)
        return (:(loop($(idxs...), $body)), pos)
    end
    parse_index_paren(s, pos)
end

function parse_index_paren(s, pos)
    if (pos′ = recognize(r"\s*\(\s*", s, pos)) !== nothing
        (res, pos) = parse_index_with(s, pos′)
        @assert (pos′ = recognize(r"\s*\)\s*", s, pos)) !== nothing
        return (res, pos′)
    end
    parse_index_assign(s, pos)
end

function parse_index_assign(s, pos)
    (ex, pos) = parse_julia_greedy(s, pos)
    return (capture_index_assign(ex), pos)
end

function capture_index_assign(ex)
    incs = Dict(:+= => +, :*= => *, :/= => /, :^= => ^)
    if haskey(incs, ex.head) && length(ex.args) == 2
        lhs = capture_index_expression(ex.args[1], false)
        rhs = capture_index_expression(ex.args[2], false)
        return :(assign($lhs, $(Literal(incs[ex.head])), $rhs))
    elseif ex.head == :comparison && length(ex.args) == 5 && ex.args[2] == :< && ex.args[4] == :>=
        lhs = capture_index_expression(ex.args[1], false)
        op = capture_index_expression(ex.args[3], false)
        rhs = capture_index_expression(ex.args[5], false)
        return :(assign($lhs, $op, $rhs))
    end
    return capture_index_expression(ex, false)
end

function capture_index_expression(ex, wrap)
    if ex isa Expr && ex.head == :call && length(ex.args) > 1 && ex.args[1] != :~
        return :(call($(map(arg -> capture_index_expression(arg, wrap), ex.args)...)))
    elseif ex isa Expr && ex.head == :ref && length(ex.args) >= 1
        tns = capture_index_expression(ex.args[1], wrap)
        return :(access($tns, $(map(arg->capture_index_expression(arg, true), ex.args[2:end])...)))
    elseif ex isa Expr && ex.head == :$ && length(ex.args) == 1
        return esc(ex.args[1])
    elseif ex isa Symbol && wrap
        return Name(ex)
    elseif wrap
        return :(Literal(esc(ex)))
    else
        return esc(ex)
    end
end

parse_index(s) = parse_index_with(s, 1)[1]

macro i_str(s)
    return parse_index(s)
end