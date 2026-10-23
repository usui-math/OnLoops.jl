import GAIO

export closed_box, closed_cover, outer_graph, recurrent_vertices, graph_core, closed_intersects

# Cells per parallel chunk in outer_graph. Chunk boundaries are where the edge
# budget is checked, so this also bounds how far a parallel run can overshoot.
const _GRAPH_CHUNK = 512

# Proof geometry is defined by exact stored domain data, NOT GAIO's rounded cells.
function _grid_geometry(grid::GAIO.BoxGrid{N,T}) where {N,T}
    N > 0 || throw(ArgumentError("grid dimension must be positive"))
    all(n -> 0 < n <= typemax(Int), grid.dims) || throw(ArgumentError("invalid grid dimensions"))
    all(isfinite, grid.domain.center) || throw(ArgumentError("nonfinite grid center"))
    all(r -> isfinite(r) && r > 0, grid.domain.radius) || throw(ArgumentError("invalid grid radius"))
    dims = map(Int, Tuple(grid.dims))
    center = map(Rational{BigInt}, Tuple(grid.domain.center))
    radius = map(Rational{BigInt}, Tuple(grid.domain.radius))
    lower = map(-, center, radius)
    step = map((r, n) -> 2*r/n, radius, dims)
    for k in 1:N
        _checked_interval(interval(T, lower[k], center[k]+radius[k]))
    end
    return (; lower, step, dims)
end

function _checked_key(dims, key)
    key isa Tuple && length(key) == length(dims) || throw(DimensionMismatch("key dimension must match grid"))
    all(j -> j isa Integer, key) || throw(ArgumentError("grid keys must be integers"))
    all(1 <= key[k] <= dims[k] for k in eachindex(dims)) || throw(BoundsError(dims, key))
    return key
end

function _closed_box(geometry, key, ::Type{T}) where {T}
    _checked_key(geometry.dims, key)
    return ntuple(length(key)) do k
        lo = geometry.lower[k] + (Int(key[k])-1)*geometry.step[k]
        _checked_interval(interval(T, lo, lo+geometry.step[k]))
    end
end

"""
    _cell_bounds(geometry, T)

Precompute, once per grid and endpoint type, the outward-rounded T bounds of
every cell boundary: `(down, up)` with `down <= B_i <= up`. A cell `j` is then
`[down(B_{j-1}), up(B_j)]`, which is the SAME tightest enclosure as
`interval(T, B_{j-1}, B_j)`. Used by the graph builder only.
"""
function _cell_bounds(geometry, ::Type{T}) where {T}
    return ntuple(length(geometry.dims)) do k
        n = geometry.dims[k]
        lo = Vector{T}(undef, n+1)
        hi = Vector{T}(undef, n+1)
        for i in 0:n
            exact = geometry.lower[k] + i*geometry.step[k]
            f = T(exact)
            isfinite(f) || throw(ArgumentError("cell boundary is not finite in $T"))
            rounded = Rational{BigInt}(f)
            if rounded == exact
                lo[i+1] = hi[i+1] = f
            elseif rounded > exact
                lo[i+1], hi[i+1] = prevfloat(f), f
            else
                lo[i+1], hi[i+1] = f, nextfloat(f)
            end
        end
        (lo, hi)
    end
end

function _cached_box(bounds, key, ::Type{T}) where {T}
    return ntuple(length(key)) do k
        interval(T, bounds[k][1][key[k]], bounds[k][2][key[k]+1])
    end
end

"""
    closed_box(grid::GAIO.BoxGrid, key)

Outward CPU interval enclosure of a canonical CLOSED grid cell. Stored domain
center/radius are interpreted as exact binary values, with exact rational cell
endpoints. Does not use GAIO's rounded cell center, left edge, or scale.
"""
closed_box(grid::GAIO.BoxGrid{N,T}, key) where {N,T} = _closed_box(_grid_geometry(grid), key, T)

function _checked_image(image, n)
    image isa Tuple && length(image) == n || throw(DimensionMismatch("image dimension must match grid"))
    all(x -> x isa Interval, image) || throw(ArgumentError("full-box images must be real intervals"))
    foreach(_checked_interval, image)
    return image
end

function _closed_cover(grid, geometry, bounds, image, max_boxes::Integer)
    max_boxes >= 0 || throw(ArgumentError("max_boxes must be nonnegative"))
    ranges, escaped = _closed_ranges(geometry, bounds, image)
    count = prod(big(length(r)) for r in ranges)
    count <= max_boxes || throw(ArgumentError("closed cover exceeds max_boxes; no partial cover returned"))
    K = keytype(typeof(grid))
    hits = Set{K}()
    if count > 0
        for key in CartesianIndices(ranges)
            push!(hits, K(Tuple(key)))
        end
    end
    return (boxes=GAIO.BoxSet(grid, hits), may_escape=escaped)
end

# Per-axis index ranges of the closed cells touching `image`, plus whether the
# image leaves the exact domain. Validates the image; the caller checks budgets.
function _closed_ranges(geometry, bounds, image)
    n = length(geometry.dims)
    _checked_image(image, n)
    per_axis = ntuple(n) do k
        size = geometry.dims[k]
        i0 = _first_boundary_ge(geometry, bounds[k], k, inf(image[k]))
        i1 = _last_boundary_le(geometry, bounds[k], k, sup(image[k]))
        lo = max(1, i0)
        hi = min(size, i1 + 1)
        # Outside parts are reported, never clipped: compare against B_0 and B_size.
        escaped = _boundary_gt(geometry, bounds[k], k, 0, inf(image[k])) ||
                  _boundary_lt(geometry, bounds[k], k, size, sup(image[k]))
        (lo > hi ? (1:0) : (lo:hi), escaped)
    end
    return (map(first, per_axis), any(last, per_axis))
end

# First boundary index i in 0:n with B_i >= value. The precomputed enclosure
# decides almost every comparison; only a value within one ulp of a boundary
# needs the exact rational test. `bounds` must be `(down, up)` from `_cell_bounds`.
function _first_boundary_ge(geometry, bounds, k, value)
    down, up = bounds
    n = geometry.dims[k]
    i = searchsortedfirst(up, value) - 1
    while i <= n
        down[i+1] >= value && return i
        if !(up[i+1] < value) &&
           geometry.lower[k] + i*geometry.step[k] >= Rational{BigInt}(value)
            return i
        end
        i += 1
    end
    return n + 1
end

# Last boundary index i in 0:n with B_i <= value.
function _last_boundary_le(geometry, bounds, k, value)
    down, up = bounds
    i = searchsortedlast(down, value) - 1
    while i >= 0
        up[i+1] <= value && return i
        if !(down[i+1] > value) &&
           geometry.lower[k] + i*geometry.step[k] <= Rational{BigInt}(value)
            return i
        end
        i -= 1
    end
    return -1
end

# Exact tests for one boundary, decided by the enclosure whenever possible.
_boundary_gt(geometry, bounds, k, i, value) =
    bounds[1][i+1] > value ||
        (!(bounds[2][i+1] <= value) &&
         geometry.lower[k] + i*geometry.step[k] > Rational{BigInt}(value))

_boundary_lt(geometry, bounds, k, i, value) =
    bounds[2][i+1] < value ||
        (!(bounds[1][i+1] >= value) &&
         geometry.lower[k] + i*geometry.step[k] < Rational{BigInt}(value))

# Exact reference implementation: Rational{BigInt} index ranges. Used by the
# public `closed_cover` and as the oracle for the fast path above.
function _closed_cover(grid, geometry, image, max_boxes::Integer)
    max_boxes >= 0 || throw(ArgumentError("max_boxes must be nonnegative"))
    n = length(geometry.dims)
    _checked_image(image, n)
    bounds = map(x -> (Rational{BigInt}(inf(x)), Rational{BigInt}(sup(x))), image)
    ranges = ntuple(n) do k
        L, h, size = geometry.lower[k], geometry.step[k], geometry.dims[k]
        lo = max(big(1), ceil(BigInt, (bounds[k][1]-L)/h))
        hi = min(big(size), floor(BigInt, (bounds[k][2]-L)/h)+1)
        lo > hi ? (1:0) : (Int(lo):Int(hi))
    end
    count = prod(big(length(r)) for r in ranges)
    count <= max_boxes || throw(ArgumentError("closed cover exceeds max_boxes; no partial cover returned"))
    K = keytype(typeof(grid))
    hits = Set{K}()
    if count > 0
        for key in CartesianIndices(ranges)
            push!(hits, K(Tuple(key)))
        end
    end
    may_escape = any(bounds[k][1] < geometry.lower[k] ||
                     bounds[k][2] > geometry.lower[k] + geometry.dims[k]*geometry.step[k] for k in 1:n)
    return (boxes=GAIO.BoxSet(grid, hits), may_escape=may_escape)
end

"""
    closed_cover(grid::GAIO.BoxGrid, image; max_boxes=1_000_000)

Return `(boxes, may_escape)` for ALL canonical closed cells touching the interval
image. Includes both neighbours at seams and the domain upper face. Outside
parts are reported, never silently clipped. Invalid intervals or exhausted
enumeration budgets throw instead of returning an incomplete cover.
"""
function closed_cover(grid::GAIO.BoxGrid, image; max_boxes::Integer=1_000_000)
    return _closed_cover(grid, _grid_geometry(grid), image, max_boxes)
end

"""
    outer_graph(f, source::GAIO.BoxSet; max_vertices=100_000, max_edges=1_000_000)

Conservative Boolean graph of full CLOSED-box images. `f` must mathematically
enclose the entire input cell, not just samples. Returns sorted `keys`, vertex
`adjacency`, domain `may_escape`, and candidate-key `may_leave` flags. Boundary
neighbours outside the key set may conservatively set `may_leave` even when the
true image is contained. `max_edges` bounds all enumerated candidate edges,
including targets outside `source`. `source.partition` must be a `GAIO.BoxGrid`.
No partial graph or proof verdict is returned.

Cells are independent, so they are processed in chunks that may run on several
threads. `f` must then be thread-safe and side-effect free. The returned keys,
adjusted adjacency, and flags are identical to a single-threaded run; the edge
budget is checked at chunk boundaries, so a parallel run may enumerate slightly
past `max_edges` before the same exception is raised.
"""
function outer_graph(f, source::GAIO.BoxSet; max_vertices::Integer=100_000, max_edges::Integer=1_000_000)
    max_vertices >= 0 && max_edges >= 0 || throw(ArgumentError("graph budgets must be nonnegative"))
    length(source.set) <= max_vertices || throw(ArgumentError("graph exceeds max_vertices"))
    grid = source.partition
    geometry = _grid_geometry(grid)
    foreach(key -> _checked_key(geometry.dims, key), source.set)
    K = keytype(typeof(grid))
    keys = sort!([K(key) for key in source.set])
    index = Dict(key => u for (u, key) in enumerate(keys))
    adjacency = [Int[] for _ in keys]
    # Byte-per-element vectors, NOT BitVectors: packing bits would make the
    # concurrent per-cell writes below lose updates.
    may_escape, may_leave = fill(false, length(keys)), fill(false, length(keys))
    hits = zeros(Int, length(keys))
    T = eltype(typeof(grid.domain))
    bounds = _cell_bounds(geometry, T)
    work = big(0)
    for start in 1:_GRAPH_CHUNK:length(keys)
        stop = min(start + _GRAPH_CHUNK - 1, length(keys))
        # Each cell is capped by the whole budget; the cumulative check below is
        # what enforces max_edges, and it runs outside the parallel region.
        fill_cell = function (u)
            image = f(_cached_box(bounds, keys[u], T))
            ranges, escaped = _closed_ranges(geometry, bounds, image)
            count = prod(big(length(r)) for r in ranges)
            count <= max_edges ||
                throw(ArgumentError("closed cover exceeds max_boxes; no partial cover returned"))
            hits[u] = Int(count)
            may_escape[u] = escaped
            may_leave[u] = escaped
            rows = adjacency[u]
            sizehint!(rows, hits[u])
            # Reversed ranges visit the keys in lexicographic order, which is the
            # order vertex ids were assigned in, so `rows` stays sorted.
            for index_key in CartesianIndices(reverse(ranges))
                v = get(index, K(reverse(Tuple(index_key))), 0)
                v == 0 ? (may_leave[u] = true) : push!(rows, v)
            end
            return nothing
        end
        if Threads.nthreads() == 1
            for u in start:stop
                fill_cell(u)
            end
        else
            _parallel_for(u -> fill_cell(u), start, stop)
        end
        work += sum(view(hits, start:stop))
    end
    work <= max_edges || throw(ArgumentError("graph exceeds max_edges; no partial graph returned"))
    return (; keys, adjacency, may_escape, may_leave)
end

# Run `body` over `start:stop` on all available threads. Task wrappers are
# unwrapped so callers still see the documented exception type; with several
# failing cells the one reported is not guaranteed to be the lowest index.
# Parallel regions never nest: a region entered from inside another one runs
# serially, which also keeps a threaded parameter job from oversubscribing.
const _PARALLEL_DEPTH = Threads.Atomic{Int}(0)

function _parallel_for(body, start::Int, stop::Int)
    if Threads.nthreads() == 1 || stop < start
        return _serial_for(body, start, stop)
    end
    nested = Threads.atomic_add!(_PARALLEL_DEPTH, 1) != 0
    try
        nested && return _serial_for(body, start, stop)
        Threads.@threads :static for u in start:stop
            body(u)
        end
    catch e
        throw(_unwrap_task_error(e))
    finally
        Threads.atomic_sub!(_PARALLEL_DEPTH, 1)
    end
    return nothing
end

function _serial_for(body, start::Int, stop::Int)
    for u in start:stop
        body(u)
    end
    return nothing
end

function _unwrap_task_error(e)
    for _ in 1:8
        e isa TaskFailedException && (e = e.task.exception; continue)
        e isa CompositeException && !isempty(e.exceptions) && (e = first(e.exceptions); continue)
        return e
    end
    return e
end

function _reverse_graph(adjacency::AbstractVector)
    n = length(adjacency)
    incoming = [Int[] for _ in 1:n]
    for u in 1:n
        adjacency[u] isa AbstractVector || throw(ArgumentError("adjacency rows must be vectors"))
        for v in adjacency[u]
            v isa Integer && 1 <= v <= n || throw(ArgumentError("invalid graph vertex reference"))
            push!(incoming[Int(v)], u)
        end
    end
    return incoming
end

"""
    recurrent_vertices(adjacency)

Sorted vertices in cyclic SCCs (size > 1, or singleton WITH a self-edge).
An outer graph's recurrent candidates are not a proof of actual recurrence.
Uses iterative Kosaraju traversal: no recursion-depth limit.
"""
function recurrent_vertices(adjacency::AbstractVector)
    incoming = _reverse_graph(adjacency)
    n = length(adjacency)
    seen, recurrent = falses(n), falses(n)
    order = Int[]
    for root in 1:n
        seen[root] && continue
        seen[root] = true
        stack = [(root, 1)]
        while !isempty(stack)
            u, j = stack[end]
            if j > length(adjacency[u])
                pop!(stack)
                push!(order, u)
            else
                stack[end] = (u, j+1)
                v = Int(adjacency[u][j])
                if !seen[v]
                    seen[v] = true
                    push!(stack, (v, 1))
                end
            end
        end
    end
    fill!(seen, false)
    for root in Iterators.reverse(order)
        seen[root] && continue
        seen[root] = true
        stack, component = [root], Int[]
        while !isempty(stack)
            u = pop!(stack)
            push!(component, u)
            for v in incoming[u]
                if !seen[v]
                    seen[v] = true
                    push!(stack, v)
                end
            end
        end
        if length(component) > 1 || root in adjacency[root]
            recurrent[component] .= true
        end
    end
    return findall(recurrent)
end

"""
    graph_core(adjacency)

Sorted vertices surviving repeated removal of vertices with no incoming OR
outgoing edge in the induced graph. Retains bi-infinite bridges between cycles,
unlike SCC recurrence. Linear-time queue deletion, not proof of true invariance.
"""
function graph_core(adjacency::AbstractVector)
    incoming = _reverse_graph(adjacency)
    n = length(adjacency)
    indegree, outdegree = length.(incoming), length.(adjacency)
    alive = trues(n)
    queue = [u for u in 1:n if indegree[u] == 0 || outdegree[u] == 0]
    j = 1
    while j <= length(queue)
        u = queue[j]
        j += 1
        alive[u] || continue
        alive[u] = false
        for v in adjacency[u]
            alive[v] || continue
            indegree[v] -= 1
            indegree[v] == 0 && push!(queue, Int(v))
        end
        for v in incoming[u]
            alive[v] || continue
            outdegree[v] -= 1
            outdegree[v] == 0 && push!(queue, v)
        end
    end
    return findall(alive)
end

"""
    closed_intersects(A::GAIO.BoxSet, B::GAIO.BoxSet)

True for contact or overlap of canonical CLOSED cells in the SAME grid. Key-set
disjointness is not geometric disjointness. Different grids are rejected.
"""
function closed_intersects(A::GAIO.BoxSet, B::GAIO.BoxSet)
    geometry = _grid_geometry(A.partition)
    A.partition == B.partition || throw(ArgumentError("closed collision requires the same canonical grid"))
    foreach(key -> _checked_key(geometry.dims, key), A.set)
    foreach(key -> _checked_key(geometry.dims, key), B.set)
    n = length(geometry.dims)
    # ponytail: quadratic pair scan; use neighbour-key lookup when large sets make it a bottleneck.
    return any(all(abs(Int(a[k])-Int(b[k])) <= 1 for k in 1:n) for a in A.set, b in B.set)
end
