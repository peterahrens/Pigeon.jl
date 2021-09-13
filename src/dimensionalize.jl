"""
dimensionalization assumes foralls have unique indices.
"""

struct DimensionalizeStyle end

function lower!(root, ctx, ::DimensionalizeStyle)
    Postwalk(node -> (dimensionalize!(node, ctx); node))(root)
    @assert !(make_style(root, ctx) isa DimensionalizeStyle)
    lower!(root, ctx)
end

dimensionalize!(node, ctx) = nothing

function dimensionalize!(node::Access, ctx)
    dims = getdims(ctx)
    if !istree(node.tns)
        for (n, (idx, lowered_axis)) in enumerate(zip(getname.(node.idxs), lower_axes(node.tns, ctx)))
            site = (getname(node.tns), n)
            if !haskey(dims, site)
                push!(dims.labels, site)
                dims.lowered_axes[site] = lowered_axis
            end
            site_axis = dims[site]
            if !haskey(dims, idx)
                push!(dims.labels, idx)
                dims.lowered_axes[union!(dims.labels, site, idx)] = site_axis
            elseif !in_same_set(dims.labels, idx, site)
                idx_axis = dims[idx]
                dims.lowered_axes[union!(dims.labels, site, idx)] = lower_axis_merge(ctx, idx_axis, site_axis)
            end
        end
    end
end

struct Dimensions
    labels
    lowered_axes
end

Dimensions() = Dimensions(DisjointSets{Any}(), Dict())

#there is a wacky julia bug that is fixed on 70cc57cb36. It causes find_root! to sometimes
#return the right index into dims.labels.revmap, but reinterprets the access as the wrong type.
#not sure which commit actually fixed this, but I need to move on with my life.
Base.getindex(dims::Dimensions, idx) = dims.lowered_axes[find_root!(dims.labels, idx)]
Base.haskey(dims::Dimensions, idx) = idx in dims.labels
function isdimensionalized(dims::Dimensions, node::Access)
    for (n, idx) in enumerate(getname.(node.idxs))
        site = (getname(node.tns), n)
        (haskey(dims, idx) && haskey(dims, site) && in_same_set(dims.labels, idx, site)) || return false
    end
    return true
end

function getdims end
function lower_axes end
function lower_axis_merge end