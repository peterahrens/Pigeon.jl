macro expand(ex)
    :(@macroexpand(ex))
end
macro expand1(ex)
    :(@macroexpand(ex))
end

macro identity(ex) ex end

macro preexpand(ex)
    @assert ex.head == :macrocall && length(ex.args) >= 1
    if length(ex.args) > 1
        return esc(Expr(:macrocall, ex.args[1], map(arg->macroexpand(__module__, arg, recursive=true), ex.args[2:end])...))
    end
end

macro preexpand1(ex)
    @assert ex.head == :macrocall && length(ex.args) >= 1
    if length(ex.args) > 1
        return esc(Expr(:macrocall, ex.args[1], map(arg->macroexpand1(__module__, arg, recursive=false), ex.args[2:end])...))
    end
end