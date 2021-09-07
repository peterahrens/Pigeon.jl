struct DefaultStyle end
struct UnknownStyle end

lower!(node, ctx) = lower!(node, ctx, make_style(node, ctx))

make_style(root, ctx) = make_style(root, ctx, root)
function make_style(root, ctx, node)
    if istree(node)
        #m = map(arg->make_style(root, ctx, arg), arguments(node))
        #r = reduce(result_style, m)
        #s = resolve_style(root, ctx, node, r)
        #@info "hmm" m r s node
        return resolve_style(root, ctx, node, mapreduce(arg->make_style(root, ctx, arg), result_style, arguments(node)))
        #return s
    end
    return DefaultStyle()
end

result_style(a, b) = _result_style(combine_style(a, b), combine_style(b, a))
_result_style(a::UnknownStyle, b::UnknownStyle) = throw(MethodError(combine_style, a, b))
_result_style(a, b::UnknownStyle) = a
_result_style(a::UnknownStyle, b) = b
_result_style(a::T, b::T) where {T} = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
_result_style(a, b) = (a == b) ? a : @assert false "TODO lower_style_ambiguity_error"
combine_style(a, b) = UnknownStyle()

combine_style(a::DefaultStyle, b) = b
resolve_style(root, ctx, node, style) = style