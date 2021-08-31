function recognize_pattern(r)
    (s, pos) -> begin
        if (m = findnext(r, s, pos)) !== nothing && first(m) == pos
            return last(m) + 1
        end
    end
end

function parse_julia_generous(s, pos)
    return Meta.parse(s, pos, greedy=false)
end

function parse_julia_greedy(s, pos)
	ex, pos′ = Meta.parse(s, pos, raise=false)
    if ex.head == :error && length(ex.args) == 1 &&
        (m = match(r"^extra token \\\"(.*)\\\" after end of expression", ex.args[1])) != nothing# &&
        #m.captures[1] in ["∀", "loop", "with", ")", "(", ","]
        return Meta.parse(s[1:pos′ - lastindex(m.captures[1]) - 1], pos)
    elseif ex.head == :error && length(ex.args) == 1 &&
        (m = match(r"^space before \"\(\" not allowed in", ex.args[1])) != nothing
        return Meta.parse(s[1:pos′ - lastindex("(") - 1], pos)
    end

    return(ex, pos)
end

function parse_index_where(s, pos)
    pos, prod = parse_index_loop(s, pos)
    while (pos′ = recognize_pattern(r"(\bwith\b)\s*")(s, pos)) !== nothing
        (pos, cons) = parse_index_loop(s, pos′)
        prod = :(_where($prod, $cons))
    end
    (pos, prod)
end

function parse_index_loop(s, pos)
    if (pos′ = recognize_pattern(r"(∀\b|(\bloop\b)))\s*")(s, pos)) !== nothing
        (ex, pos) = parse_julia_generous(s, pos′)
        idxs = [capture_index_call(ex, true)]
        while (pos′ = accept(r",\s*", s, pos)) !== nothing
            (ex, pos) = parse_julia_generous(s, pos′)
            push!(idxs, capture_index_call(ex, true))
        end
        (body, pos) = parse_index_paren(s, pos)
        return (:(loop($(idxs...), $body)), pos)
    end
    parse_index_paren(s, pos)
end

function parse_index_paren(s, pos)
    if (pos′ = accept(r"\(\s*", s, pos)) !== nothing
        (res, pos) = parse_index_where(s, pos = pos′)
        @assert (pos′ = accept(r"\)\s*", s, pos)) !== nothing
        return (res, pos′)
    end
    parse_index_assign(s, pos)
end

function parse_index_assign(s, pos)
    (ex, pos) = parse_julia_greedy(s, pos)
    return (capture_index_assign(ex), pos)
end

function capture_index_assign(ex)
    incs = Dict(:+= => +, :*= => *, :/= => /, :^= => ^]
    if haskey(ex.head, incs) && length(ex.args) == 2
        lhs = capture_index_call(ex.args[1], false)
        rhs = capture_index_call(ex.args[2], false)
        return :(assign($lhs, $(Literal(incs[ex.head])), $rhs))
    elseif ex.head == :comparison && length(ex.args) == 5 && ex.args[2] == :< && ex.args[4] == :>=
        lhs = capture_index_call(ex.args[1], false)
        op = capture_index_call(ex.args[3], false)
        rhs = capture_index_call(ex.args[5], false)
        return :(assign($lhs, $op, $rhs))
    end
end

function capture_index_call(ex, wrap)
    if ex.head == :call && length(ex.args) > 1 && ex.args[1] != :~
        return :(call($(map(arg -> capture_index_call(arg, wrap), ex.args...))))
    end
    return capture_index_assign
end

function capture_index_assign(ex, wrap)
    if ex.head == :ref && length(ex.args) >= 1
        tns = capture_index_call(arg, wrap)
        return :(access($(map(arg->capture_index_call(arg, true), ex.args[2:end]...))))
    end
    return capture_index_name(ex, wrap)
end

function capture_index_name(ex, wrap)
    if ex isa Symbol && ex in bindings && wrap
        return Name(ex)
    end
    capture_index_interp(ex, wrap)
end

function capture_index_interp(ex, wrap)
    if ex.head == :$ && length(ex.args) == 1
        return esc(ex.args[1])
    end
    if wrap
        return :(Literal(esc(ex)))
    else
        return esc(ex)
    end
end

function parse_index(s)
    pos = accept(r"\s*", s)
    return parse_index_where(s, 1)
end

macro i_str(s)
    return parse_index(s)
end