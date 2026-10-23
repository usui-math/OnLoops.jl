# Step S2: an enclosure of K_p, the set of bounded orbits, for every parameter p
# in one closed parameter box.
#
# The enclosure is a graph on state boxes. Its guarantee: for every p in the box
# and every bounded orbit (z_n) of H_p there are cells k_n with z_n in B_{k_n},
# (k_n, k_{n+1}) an edge, and Re x_n + i Im x_n in that edge's x box. Each
# function below removes a cell, an edge or part of a box only when no such
# orbit can use it.

const MAX_CELLS = 3_000_000
const MAX_EDGES = 120_000_000

"""
    refine(keys)

The 16 children of every cell when each axis of the grid is halved.
"""
refine(keys) = Set(ntuple(j -> 2Int(k[j]) - 1 + o[j], 4)
                   for k in keys for o in Iterators.product(0:1, 0:1, 0:1, 0:1))

"""
    henon_inverse(z, p)

`H_p^{-1}(X, Y) = (Y, (Y^2 + c - X)/a)` in real coordinates. Only valid for real
`a` (`Im a = 0`); every caller checks this.
"""
henon_inverse(z, p) = (z[3], z[4],
                       (z[3]^2 - z[4]^2 + p[3] - z[1]) / p[1],
                       ((z[3] + z[3]) * z[4] + p[4] - z[2]) / p[1])

function require_real_a(p)
    require(inf(p[2]) == sup(p[2]) == 0, "the inverse map and box shrinking need real a (Im a = 0)")
    require(!(inf(p[1]) <= 0 <= sup(p[1])), "the parameter box must exclude a = 0")
end

function require_cell_graph(graph)
    require_real_a(graph.parameters)
    require(OnLoops._henon_radius(OnLoops._henon_data(graph.parameters), graph.radius) == graph.radius,
            "the grid radius must be a valid Lemma 11 radius for the whole parameter box")
    require(graph.n >= 8 && ispow2(graph.n), "cells per axis must be a power of two, at least 8")
    require(all(k -> length(k) == 4 && all(j -> 1 <= k[j] <= graph.n, 1:4), graph.keys),
            "cell keys must lie in the grid")
end

"""
    remove_edges_without_inverse(graph)

Drop the edge `v -> w` when cell `v` does not touch the closed-box image of
cell `w` under `H^{-1}`: a true transition `z -> H(z)` with `H(z)` in `B_w` has
`z = H^{-1}(H(z))` in that image. Then keep only the `graph_core`.
"""
function remove_edges_without_inverse(graph)
    require_cell_graph(graph)
    p = graph.parameters
    geometry = OnLoops._grid_geometry(state_grid(graph.radius, graph.n))
    bounds = OnLoops._cell_bounds(geometry, Float64)
    preimage_ranges = map(graph.keys) do key
        preimage = henon_inverse(OnLoops._cached_box(bounds, key, Float64), p)
        first(OnLoops._closed_ranges(geometry, bounds, preimage))
    end
    touches_preimage(v, w) = all(j -> graph.keys[v][j] in preimage_ranges[w][j], 1:4)
    adjacency = [[w for w in graph.adjacency[v] if touches_preimage(v, w)] for v in eachindex(graph.keys)]
    core = graph_core(adjacency)
    require(!isempty(core), "empty graph core after the inverse-image test")
    return merge(graph, (keys=graph.keys[core], adjacency=induced_subgraph(adjacency, core)))
end

"""
    global_cover(p; max_level=7)

Cell graph on the uniform `2^max_level` grid of `[-r, r]^4`, `r = henon_radius(p)`
(Lemma 11: every bounded orbit stays in this cube). Starts from all `8^4`
cells. At each level it keeps the `graph_core` of the closed-box image graph,
applies `remove_edges_without_inverse`, and halves the surviving cells.
Returns `(; parameters, radius, n, keys, adjacency)`.
"""
function global_cover(p; max_level=7)
    radius = henon_radius(p)
    graph = nothing
    for level in 3:max_level
        n = 2^level
        grid = state_grid(radius, n)
        if isnothing(graph)
            candidates = GAIO.cover(grid, :)
        else
            require(16big(length(graph.keys)) <= MAX_CELLS, "refined cover exceeds the cell budget")
            candidates = GAIO.BoxSet(grid, refine(graph.keys))
        end
        forward = outer_graph(z -> henon(z, p), candidates; max_vertices=MAX_CELLS, max_edges=MAX_EDGES)
        core = graph_core(forward.adjacency)
        require(!isempty(core), "empty graph core; bounded orbits are not covered")
        graph = (parameters=p, radius=radius, n=n, keys=forward.keys[core],
                 adjacency=induced_subgraph(forward.adjacency, core))
        graph = remove_edges_without_inverse(graph)
        println((n=n, candidates=length(candidates.set), core=length(graph.keys),
                 edges=sum(length, graph.adjacency)))
        flush(stdout)
    end
    return graph
end

"""
    square_root_in(I, T)

Enclosure of `{s in I : s^2 in T}`, or `nothing` when it is empty.
"""
function square_root_in(I, T)
    require(!isnai(I) && !isnai(T) && isguaranteed(I) && isguaranteed(T), "invalid interval")
    sup(T) < 0 && return nothing
    root = sqrt(interval(Float64, max(0.0, inf(T)), sup(T)))
    if inf(I) >= 0
        result = intersect_interval(I, root)
    elseif sup(I) <= 0
        result = intersect_interval(I, -root)
    else
        result = intersect_interval(I, interval(Float64, -sup(root), sup(root)))
    end
    return isempty_interval(result) ? nothing : result
end

function require_guaranteed(intervals...)
    require(all(I -> !isnai(I) && isguaranteed(I), intervals), "interval arithmetic lost its guarantee")
end

"""
    shrink_edge(source, target, p; passes=4)

Smaller boxes `(source', target')` that still contain every pair `(z, H_p(z))`
with `z` in `source`, `H_p(z)` in `target` and `p` in the parameter box, or
`nothing` when no such pair exists. With `x = xr + i xi`, `y = yr + i yi`:

    target x = x^2 + c - a y,   target y = x.

Each pass solves these equations for every variable in turn and intersects:
`Xr, Xi` from the first equation; `yr, yi` from it again (division by `a`);
`square_re = xr^2 - xi^2` and `square_im = 2 xr xi` from it once more; then
`xr, xi` from those two squares (`square_root_in`) and from the product
`xr xi = square_im/2` when the other factor excludes zero.
Requires real `a` with `a != 0`.
"""
function shrink_edge(source, target, p; passes=4)
    require(all(is_valid_interval, (source..., target..., p...)), "boxes and parameters must be valid intervals")
    require_real_a(p)
    a, cr, ci = p[1], p[3], p[4]
    xr = intersect_interval(source[1], target[3])
    xi = intersect_interval(source[2], target[4])
    (isempty_interval(xr) || isempty_interval(xi)) && return nothing
    yr, yi = source[3], source[4]
    Xr, Xi = target[1], target[2]
    for _ in 1:passes
        Xr = intersect_interval(Xr, xr^2 - xi^2 + cr - a*yr)
        Xi = intersect_interval(Xi, (xr + xr)*xi + ci - a*yi)
        require_guaranteed(Xr, Xi)
        (isempty_interval(Xr) || isempty_interval(Xi)) && return nothing
        yr = intersect_interval(yr, (xr^2 - xi^2 + cr - Xr)/a)
        yi = intersect_interval(yi, ((xr + xr)*xi + ci - Xi)/a)
        require_guaranteed(yr, yi)
        (isempty_interval(yr) || isempty_interval(yi)) && return nothing
        square_re = Xr - cr + a*yr
        square_im = Xi - ci + a*yi
        xr = square_root_in(xr, square_re + xi^2)
        isnothing(xr) && return nothing
        xi = square_root_in(xi, xr^2 - square_re)
        isnothing(xi) && return nothing
        product = square_im/interval(Float64, 2)
        if inf(xi) > 0 || sup(xi) < 0
            xr = intersect_interval(xr, product/xi)
            require_guaranteed(xr)
            isempty_interval(xr) && return nothing
        end
        if inf(xr) > 0 || sup(xr) < 0
            xi = intersect_interval(xi, product/xr)
            require_guaranteed(xi)
            isempty_interval(xi) && return nothing
        end
    end
    return ((xr, xi, yr, yi), (Xr, Xi, xr, xi))
end

"""
    shrink_cover(graph; passes=15)

Turn the cell graph of `global_cover` into the box enclosure used by the cone
check. Each pass shrinks every edge with `shrink_edge`, replaces every box by
its intersection with the hull of its shrunk outgoing sources and the hull of
its shrunk incoming targets, drops cells left without an edge or with an empty
box, and keeps the `graph_core`. Every bounded orbit passes through an
outgoing and an incoming edge of each cell it visits, so it stays enclosed.

Returns `(; parameters, parameter_center, parameter_deviation, radius, n, cells,
boxes, edges, edge_x_boxes)`. `edge_x_boxes[e]` is the exact rational
rectangle `(xr_lo, xr_hi, xi_lo, xi_hi)` containing `x` at the source of edge `e`.
"""
function shrink_cover(graph; passes=15)
    require_cell_graph(graph)
    p = graph.parameters
    bounds = OnLoops._cell_bounds(OnLoops._grid_geometry(state_grid(graph.radius, graph.n)), Float64)
    cells = copy(graph.keys)
    boxes = [OnLoops._cached_box(bounds, k, Float64) for k in cells]
    adjacency = graph.adjacency
    for pass in 1:passes
        outgoing_hull = Vector{Union{Nothing,StateBox}}(nothing, length(cells))
        incoming_hull = Vector{Union{Nothing,StateBox}}(nothing, length(cells))
        surviving_edges = [Int[] for _ in cells]
        for v in eachindex(cells), w in adjacency[v]
            pair = shrink_edge(boxes[v], boxes[w], p; passes=2)
            isnothing(pair) && continue
            push!(surviving_edges[v], w)
            outgoing_hull[v] = isnothing(outgoing_hull[v]) ? pair[1] : map(hull, outgoing_hull[v], pair[1])
            incoming_hull[w] = isnothing(incoming_hull[w]) ? pair[2] : map(hull, incoming_hull[w], pair[2])
        end
        alive = fill(true, length(cells))
        for v in eachindex(cells)
            if isnothing(outgoing_hull[v]) || isnothing(incoming_hull[v])
                alive[v] = false
                continue
            end
            box = ntuple(j -> intersect_interval(intersect_interval(boxes[v][j], outgoing_hull[v][j]),
                                                 incoming_hull[v][j]), 4)
            require_guaranteed(box...)
            if any(isempty_interval, box)
                alive[v] = false
            else
                boxes[v] = box
            end
        end
        surviving_edges = [alive[v] ? [w for w in surviving_edges[v] if alive[w]] : Int[] for v in eachindex(cells)]
        core = graph_core(surviving_edges)
        require(!isempty(core), "empty graph core while shrinking boxes")
        adjacency = induced_subgraph(surviving_edges, core)
        cells, boxes = cells[core], boxes[core]
        println((pass=pass, vertices=length(cells), edges=sum(length, adjacency)))
        flush(stdout)
    end
    edges = Tuple{Int,Int}[]
    edge_x_boxes = NTuple{4,Q}[]
    for v in eachindex(cells), w in adjacency[v]
        pair = shrink_edge(boxes[v], boxes[w], p; passes=4)
        isnothing(pair) && continue
        xr, xi = pair[1][1], pair[1][2]
        push!(edges, (v, w))
        push!(edge_x_boxes, (Q(inf(xr)), Q(sup(xr)), Q(inf(xi)), Q(sup(xi))))
    end
    require(!isempty(edges), "no edge survives the final shrinking")
    center, deviation = OnLoops._cone_parameter_enclosure(p)
    return (parameters=p, parameter_center=center, parameter_deviation=deviation,
            radius=graph.radius, n=graph.n, cells=cells, boxes=boxes,
            edges=edges, edge_x_boxes=edge_x_boxes)
end
