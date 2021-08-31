struct DefaultStyle end
struct UnknownStyle end

make_style(lwr, root) = make_style(lwr, root, root)
function make_style(lwr, root, node)
    if istree(node)
        #m = map(arg->make_style(lwr, root, arg), arguments(node))
        #r = reduce(result_style, m)
        #s = resolve_style(lwr, root, node, r)
        #@info "hmm" m r s node
        return resolve_style(lwr, root, node, mapreduce(arg->make_style(lwr, root, arg), result_style, arguments(node)))
        #return s
    end
    return DefaultStyle()
end

result_style(a, b) = _result_style(combine_style(a, b), combine_style(b, a))
_result_style(a::UnknownStyle, b::UnknownStyle) = throw(MethodError(combine_style, a, b))
_result_style(a, b::UnknownStyle) = a
_result_style(a::UnknownStyle, b) = b
_result_style(a::T, b::T) with {T} = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
_result_style(a, b) = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
combine_style(a, b) = UnknownStyle()

combine_style(a::DefaultStyle, b) = b
resolve_style(lwr, root, node, style) = style