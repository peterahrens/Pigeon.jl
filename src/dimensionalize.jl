"""
dimensionalization assumes foralls have unique indices.

bindings is a mapping from index->tensor, pos
"""

function dimensionalize(prgm, ctx)
    idx_sites = Dict()
    lowered_axes = Dict()
    Postwalk(node -> (dimensionalize!(node, ctx, idx_sites, lowered_axes); node))(prgm)

    idx_jdx = DisjointSets{Union{Symbol, Freshie}}(collect(keys(idx_sites))) #TODO type this as Any when you resolve DisjointSets #755

    site_jdx = Dict()

    for (idx, sites) in idx_sites
        for site in sites
            union!(idx_jdx, idx, get!(site_jdx, site, idx))
        end
    end

    jdx_sites = Dict()

    for (idx, sites) in idx_sites
        jdx = find_root!(idx_jdx, idx)
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

dimensionalize!(node, ctx, idx_sites, lowered_axes) = nothing

function dimensionalize!(node::Access, ctx, idx_sites, lowered_axes)
    if !istree(node.tns)
        for (n, idx) in enumerate(node.idxs)
            push!(get!(idx_sites, getname(idx), []), (getname(node.tns), n))
        end
        for (n, axis) in enumerate(lower_axes(node.tns, ctx))
            lowered_axes[(getname(node.tns), n)] = axis
        end
    end
end

function lower_axes end
function lower_axis_merge end