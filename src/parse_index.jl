function recognize(r, s, pos)
    if (m = findnext(r, s, pos)) !== nothing && first(m) == pos
        return last(m) + 1
    end
end

function pretty_position(s, pos)
    line = 1 + count("\n", s[1:pos])
    col = pos - ((m = findprev("\n", s, pos)) === nothing ? 1 : first(m))
    col = length(s[1:col]) #decodeunitify, only approximately right.
    count("\n", s) == 0 ? "column $col" : "line $line, column $col"
end

function parse_julia(s, pos; ctx...)
    if ctx.data.greedy
        ex, pos′ = Meta.parse(s, pos, raise=false)
        if ex isa Expr && ex.head == :error && length(ex.args) == 1 &&
            (m = match(r"^extra token \\\"(.*)\\\" after end of expression", ex.args[1])) != nothing &&
            m.captures[1] in ["loop", "with", ")", "("]
            return Meta.parse(s[1:pos′ - ncodeunits(m.captures[1]) - 1], pos)
        elseif ex isa Expr && ex.head == :error && length(ex.args) == 1 &&
            (m = match(r"^space before \"\(\" not allowed in", ex.args[1])) != nothing
            return Meta.parse(s[1:pos′ - ncodeunits("(") - 1], pos)
        elseif ex isa Expr && ex.head == :error && length(ex.args) == 1 &&
            (m = match(r"^invalid character \"(.*)\" near", ex.args[1])) != nothing && 
            m.captures[1] in ["∀",]
            return parse_julia(s[1:pos′ - ncodeunits(m.captures[1]) - 1], pos; ctx...)
        elseif (ex isa Expr && (ex.head == :error || ex.head == :incomplete)) || ex === nothing
            return (ex, nothing)
        end
        return (ex, pos′)
    else
        (ex, pos′) = Meta.parse(s, pos, greedy=false, raise=false)
        if (ex isa Expr && (ex.head == :error || ex.head == :incomplete)) || ex === nothing
            return (ex, nothing)
        end
        return (ex, pos′)
    end
end

function parse_index_with(s, pos; ctx...)
    (prod, pos) = parse_index_loop(s, pos; ctx...)
    while (pos′ = recognize(r"\s*(\bwith\b)\s*", s, pos)) !== nothing
        (cons, pos) = parse_index_loop(s, pos′; ctx...)
        prod = :(with($prod, $cons))
    end
    (prod, pos)
end

function parse_index_loop(s, pos; ctx...)
    if (pos′ = recognize(r"\s*(∀|(\bloop\b))\s*", s, pos)) !== nothing
        idx, pos = parse_index_assign(s, pos′; ctx..., greedy=false, namify=true, literalize=true)
        idxs = [idx]
        while (pos′ = recognize(r",\s*", s, pos)) !== nothing
            idx, pos = parse_index_assign(s, pos′; ctx..., greedy=false, namify=true, literalize=true)
            push!(idxs, idx)
        end
        body, pos = parse_index_loop(s, pos; ctx...)
        return (:(loop($(idxs...), $body)), pos)
    end
    parse_index_assign(s, pos; ctx...)
end

function parse_index_assign(s, pos; ctx...)
    if ((ex, pos′) = parse_julia(s, pos; ctx...); pos′ !== nothing)
        return (capture_index_assign(ex; ctx...), pos′)
    end
    parse_index_paren(s, pos; ctx...)
end

function parse_index_paren(s, pos; ctx...)
    if (pos′ = recognize(r"\s*\(\s*", s, pos)) !== nothing
        (res, pos) = parse_index_with(s, pos′; ctx..., greedy=true)
        (pos′ = recognize(r"\s*\)\s*", s, pos)) !== nothing ||
            throw(ArgumentError("missing \")\" at $(pretty_position(s, pos))"))
        return (res, pos′)
    end
    throw(ArgumentError("unrecognized input at $(pretty_position(s, pos))"))
end

function capture_index_assign(ex; ctx...)
    incs = Dict(:+= => :+, :*= => :*, :/= => :/, :^= => :^)
    if ex isa Expr && ex.head == :(=) && length(ex.args) == 2
        lhs = capture_index_expression(ex.args[1]; ctx..., mode=Write())
        rhs = capture_index_expression(ex.args[2]; ctx...)
        return :(assign($lhs, $rhs))
    elseif ex isa Expr && haskey(incs, ex.head) && length(ex.args) == 2
        lhs = capture_index_expression(ex.args[1]; ctx..., mode=Update())
        rhs = capture_index_expression(ex.args[2]; ctx...)
        op = capture_index_expression(incs[ex.head]; ctx..., namify=false, literalize=true)
        return :(assign($lhs, $op, $rhs))
    elseif ex isa Expr && ex.head == :comparison && length(ex.args) == 5 && ex.args[2] == :< && ex.args[4] == :>=
        lhs = capture_index_expression(ex.args[1]; ctx..., mode=Update())
        op = capture_index_expression(ex.args[3]; ctx..., namify=false, literalize=true)
        rhs = capture_index_expression(ex.args[5]; ctx...)
        return :(assign($lhs, $op, $rhs))
    end
    return capture_index_expression(ex; ctx...)
end

#I don't know why this is obvious but it is?
#functions get literalized
#arguments get namified and literalized
#tensors don't get wrapped at all
#indices get namified and literalized
function capture_index_expression(ex; ctx...)
    if ctx.data.slot && ex isa Expr && ex.head == :call && length(ex.args) == 2 && ex.args[1] == :~ &&
        ex.args[2] isa Symbol
        return esc(ex)
    elseif ctx.data.slot && ex isa Expr && ex.head == :call && length(ex.args) == 2 && ex.args[1] == :~ &&
        ex.args[2] isa Expr && ex.args[2].head == :call && length(ex.args[2].args) == 2 && ex.args[2].args[1] == :~ &&
        ex.args[2].args[2] isa Symbol
        return esc(ex)
    elseif ex isa Expr && ex.head == :call && length(ex.args) >= 1
        op = capture_index_expression(ex.args[1]; ctx..., namify=false, literalize=true, mode=Read())
        return :(call($op, $(map(arg->capture_index_expression(arg; ctx..., namify=true, literalize=true, mode=Read()), ex.args[2:end])...)))
    elseif ex isa Expr && ex.head == :ref && length(ex.args) >= 1
        tns = capture_index_expression(ex.args[1]; ctx..., namify=false, literalize=false, mode=Read())
        return :(access($tns, $(ctx.data.mode), $(map(arg->capture_index_expression(arg; ctx..., namify=true, literalize=true, mode=Read()), ex.args[2:end])...)))
    elseif ex isa Expr && ex.head == :$ && length(ex.args) == 1
        return esc(ex.args[1])
    elseif ex isa Symbol && ctx.data.namify
        return Name(ex)
    elseif ctx.data.pattern && ctx.data.literalize
        return esc(Expr(:$, :(Literal($ex))))
    elseif ctx.data.literalize
        return esc(:(Literal($ex)))
    else
        return esc(ex)
    end
end

function parse_index(s; namify=true, literalize=true, pattern=false, greedy=true, slot = false, mode = Read())
    ex, pos′ = parse_index_with(s, 1; namify=namify, literalize=literalize, slot=slot, pattern=pattern, greedy=greedy, mode=mode)
    if pos′ != ncodeunits(s) + 1
        throw(ArgumentError("unexpected input at $(pretty_position(s, pos′))"))
    end
    return ex
end

macro i_str(s, flags...)
    flags = isempty(flags) ? [] : flags[1]
    return parse_index(s; pattern = ('p' in flags), slot = ('p' in flags) | ('c' in flags))
end