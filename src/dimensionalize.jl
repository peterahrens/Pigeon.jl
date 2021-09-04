function axes(program)
    Postwalk()(program) do node


end
function gather_axes(node::Access)
    dict(declare_axes())
end
declare_axes(tns)