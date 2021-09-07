"""
dimensionalization assumes foralls have unique indices.

bindings is a mapping from index->tensor, pos
"""

function dimensionalize_index(prgm, ctx)
    idx_sites = Dict()
    lowered_axes = Dict()
    Postorder(node -> (dimensionalize_index!(node, ctx, idx_sites, lowered_axes); node))

    idx_jdx = DisjointSets(keys(idx_sites))

    site_jdx = Dict()

    for (idx, sites) in idx_sites
        for site in sites
            union!(idx_jdx, idx, get!(site_jdx, site, idx))
        end
    end

    jdx_sites = Dict()

    for (idx, sites) in idx_sites
        jdx = find_root!(idx_jdx)
        jdx_sites[jdx] = vcat(get(jdx_sites, jdx, []), sites)
    end

    jdx_lowered_axes = Dict()

    for (jdx, sites) in jdx_sites
        jdx_lowered_axes[jdx] = mapreduce(
            site -> lowered_axes[site],
            (axis_a, axis_b) -> lower_axis_merge(ctx, axis_a, axis_b),
            unique(sites))
    end

    return jdx_lowered_axes
end

dimensionalize_index!(node, ctx, bindings) = nothing

function dimensionalize_index!(node::Access, ctx, bindings)
    if !istree(node.tns)
        for (n, idx) in enumerate(node.idxs))
            push!(get(idx_sites, getname(idx)), (getname(tns), n))
        end
        for (n, axis) in enumerate(lower_axes(node.tns, ctx))
            lowered_axes[(getname(tns), n)] = axis
        end
    end
end

function axes(program)
    Postwalk()(program) do node
end
function gather_axes(node::Access)
    dict(declare_axes())
end
declare_axes(tns)