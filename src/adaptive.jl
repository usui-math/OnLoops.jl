# Adaptive (restricted) closed lattice for the base-coordinate dominance test.
# The union of the cells must stay an outer enclosure of the actual global chain
# recurrent set at every step, so a cell may only be replaced by an EXACT
# partition of itself: no centre-based and no volumetric shrinking anywhere.

# Dyadic start level of a fresh adaptive lattice: 2^2 = 4 cells per axis.
const _ADAPTIVE_START_LEVEL = 2

# Dyadic closed rectangle in (Re x, Im x, Re y, Im y) with exact rational bounds.
struct _FixedBox
    lo::NTuple{4,Rational{BigInt}}
    hi::NTuple{4,Rational{BigInt}}
end

_fixed_interval(box::_FixedBox, k) = interval(Rational{BigInt}, box.lo[k], box.hi[k])

_fixed_image(box::_FixedBox, parameters) = henon(ntuple(k -> _fixed_interval(box, k), 4), parameters)

# Lower bound on |x| over the box, from exact endpoint tests.
_fixed_x_lower(box::_FixedBox) = first(_modulus_bounds(_fixed_interval(box, 1), _fixed_interval(box, 2)))

function _fixed_children(box::_FixedBox)
    children = _FixedBox[box]
    for k in 1:4
        children = [child for parent in children for child in _split_fixed_axis(parent, k)]
    end
    return children
end

function _split_fixed_axis(box::_FixedBox, k::Int)
    mid = (box.lo[k] + box.hi[k])//2
    return (_FixedBox(box.lo, ntuple(j -> j == k ? mid : box.hi[j], 4)),
            _FixedBox(ntuple(j -> j == k ? mid : box.lo[j], 4), box.hi))
end

# Exact closed-box contact of the image with a candidate cell.
_fixed_meets(image, box::_FixedBox) =
    all(k -> Rational{BigInt}(inf(image[k])) <= box.hi[k] &&
             box.lo[k] <= Rational{BigInt}(sup(image[k])), 1:4)

# Uniform `level`-fold bisection of `[-r, r]^4`, in lexicographic cell order.
function _fixed_initial(r::Real, level::Int)
    n = 2^level
    step = 2*Rational{BigInt}(r)//n
    lower = -Rational{BigInt}(r)
    return [_FixedBox(ntuple(k -> lower + (index[k]-1)*step, 4),
                      ntuple(k -> lower + index[k]*step, 4))
            for index in vec(collect(CartesianIndices(ntuple(_ -> n, 4))))]
end

# Start cells of the adaptive lattice plus their grid scales and the exact
# rational domain edge they were generated from.
_fixed_start(r::Real, level::Int) =
    (_fixed_initial(r, level), fill(ntuple(_ -> 2^level, 4), 16^level), Rational{BigInt}(r))

# Cells of a uniform `dims` partition of `[-r, r]^4` as fixed boxes. Used so the
# adaptive refinement can continue from the uniform base graph's own cover
# instead of recomputing an identical first level.
function _base_fixed_boxes(base::GAIO.BoxSet)
    geometry = _grid_geometry(base.partition)
    length(geometry.dims) == 4 || throw(DimensionMismatch("Hénon base dimension must be four"))
    return [_FixedBox(ntuple(k -> geometry.lower[k] + (Int(key[k])-1)*geometry.step[k], 4),
                      ntuple(k -> geometry.lower[k] + Int(key[k])*geometry.step[k], 4))
            for key in sort!([Tuple(key) for key in base.set])]
end

_base_fixed_scales(base::GAIO.BoxSet) = fill(map(Int, Tuple(base.partition.dims)), length(base.set))

# Index bound of an `n`-cell grid for the boundary value `value`: the smallest
# `i >= 0` with `-r + 2ri/n >= value`, clamped to `0:n`. Zero is always valid.
function _fixed_boundary_index(value::Rational{BigInt}, r::Rational{BigInt}, n::Int)
    i = ceil((value + r)*n//(2r))
    return Int(clamp(i, 0, n))
end

# Span of cell indices on an `n`-cell grid that can meet the interval `lo <= t <= hi`.
function _fixed_image_cells(lo::Rational{BigInt}, hi::Rational{BigInt}, r::Rational{BigInt}, n::Int)
    lo > hi && return 1:0  # empty interval: no cell can meet it
    # Cell `j` is indexed 1..n and spans boundaries j-1..j.
    return max(1, _fixed_boundary_index(lo, r, n)):min(n, _fixed_boundary_index(hi, r, n) + 1)
end

# Index dictionaries per grid scale, kept as per-axis SORTED key lists. Cell `j`
# of an `n`-cell grid covers `[-r + (j-1)h, -r + jh]` with `h = 2r/n`, so its index
# comes from the exact grid formula; `ceil(lo * n / (2r))` is not equivalent and is
# wrong whenever the radius is not a dyadic rational. The sorted lists let an axis
# range be rejected by binary search before any candidate is examined, which matters
# because a refined lattice has many levels whose index ranges are huge compared
# with the number of cells actually present.
function _fixed_index(boxes, scales, r)
    axes = Dict{NTuple{4,Int},NTuple{4,Vector{Int}}}()
    cells = Dict{NTuple{4,Int},Vector{Tuple{NTuple{4,Int},Int}}}()
    for c in eachindex(boxes)
        scale, box = scales[c], boxes[c]
        key = ntuple(k -> Int(fld(box.lo[k] + r, 2r//scale[k])) + 1, 4)
        if !haskey(cells, scale)
            axes[scale] = ntuple(_ -> Int[], 4)
            cells[scale] = Tuple{NTuple{4,Int},Int}[]
        end
        push!(cells[scale], (key, c))
        for k in 1:4
            push!(axes[scale][k], key[k])
        end
    end
    foreach(scale -> foreach(sort!, axes[scale]), collect(keys(axes)))
    return (; axes, cells)
end

# Witness graph: vertex `c` has the edge `c -> d` when the image of cell `c`
# meets cell `d`. Cells live on several grids, so every grid's index dictionary is
# queried with the image scaled to THAT grid; the exact contact test then rejects
# the candidates the over-approximate lookup returned.
function _fixed_graph(boxes, scales, parameters, r)
    r = Rational{BigInt}(r)
    index = _fixed_index(boxes, scales, r)
    images = Vector{Any}(undef, length(boxes))
    fill_image = c -> (images[c] = _fixed_image(boxes[c], parameters); nothing)
    _parallel_for(fill_image, 1, length(boxes))
    adjacency = [Int[] for _ in boxes]
    for c in eachindex(boxes)
        image = images[c]
        seen = Set{Int}()
        for (scale, axis) in index.axes
            ranges = ntuple(4) do k
                _fixed_image_cells(Rational{BigInt}(inf(image[k])),
                                   Rational{BigInt}(sup(image[k])), r, scale[k])
            end
            # Skip a grid as soon as one axis holds no cell in range.
            empty_axis = any(1:4) do k
                cell_range = ranges[k]
                isempty(cell_range) ||
                    searchsortedfirst(axis[k], first(cell_range)) > searchsortedlast(axis[k], last(cell_range))
            end
            empty_axis && continue
            for (key, d) in index.cells[scale]
                all(k -> first(ranges[k]) <= key[k] <= last(ranges[k]), 1:4) || continue
                d in seen && continue
                if _fixed_meets(image, boxes[d])
                    push!(seen, d)
                    push!(adjacency[c], d)
                end
            end
        end
    end
    return adjacency
end

# Adaptive refinement of a starting closed lattice. `seed_boxes`/`seed_scales`
# must already enclose the actual global chain recurrent set, which the uniform
# base graph's recurrent cells do.
#
# Cells whose |x| lower bound cannot pass the test are refined. Kernel cells come
# first; when the whole kernel already passes but the bound still fails, a PRUNED
# cell is what keeps reaching the kernel region, so those are refined too.
# Refining a pruned cell is sound: subdivision only replaces a cell by an exact
# partition of itself, so the enclosure can only shrink.
function _adaptive_refine(seed_boxes::Vector{_FixedBox}, seed_scales::Vector{NTuple{4,Int}},
                          parameters, r, K; max_level::Integer=16,
                          max_cells::Integer=4000, max_levels::Integer=40,
                          max_stalls::Integer=2)
    thresh = Rational{BigInt}(K)^2
    domain = Rational{BigInt}(r)
    boxes, scales = seed_boxes, seed_scales
    status, reason = :undetermined, "adaptive lattice reached the level limit"
    min_x, best, stalls = nothing, nothing, 0
    for _ in 1:max_levels
        core = graph_core(_fixed_graph(boxes, scales, parameters, domain))
        isempty(core) && ((status, reason) = (:undetermined, "adaptive lattice pruned every cell"); break)
        min_x = minimum(_fixed_x_lower(boxes[c]) for c in core)
        4*min_x^2 > thresh && ((status, reason) = (:proved, "adaptive base dominance"); break)
        # A cube whose actual set reaches the origin keeps min|x| at zero while
        # refinement only multiplies cells; the bound is the only signal that the
        # lattice is making progress, and it does not move in that case.
        if best === nothing || min_x > best
            best, stalls = min_x, 0
        else
            stalls += 1
            stalls >= max_stalls &&
                ((status, reason) = (:undetermined, "adaptive lattice bound is not improving"); break)
        end
        refine = [c for c in core
                  if 4*_fixed_x_lower(boxes[c])^2 <= thresh && maximum(scales[c]) < 2^max_level]
        if isempty(refine)
            refine = [c for c in eachindex(boxes)
                      if 4*_fixed_x_lower(boxes[c])^2 <= thresh && maximum(scales[c]) < 2^max_level]
        end
        isempty(refine) &&
            ((status, reason) = (:undetermined, "adaptive lattice cannot refine the core"); break)
        sort!(refine, by=c -> (_fixed_x_lower(boxes[c]), -maximum(scales[c])))
        chosen = Set(refine)
        next_boxes, next_scales = _FixedBox[], NTuple{4,Int}[]
        for c in eachindex(boxes)
            if c in chosen
                append!(next_boxes, _fixed_children(boxes[c]))
                append!(next_scales, fill(scales[c] .* 2, 16))
            else
                push!(next_boxes, boxes[c])
                push!(next_scales, scales[c])
            end
        end
        length(next_boxes) <= max_cells ||
            ((status, reason) = (:undetermined, "adaptive lattice exceeds max_cells"); break)
        boxes, scales = next_boxes, next_scales
    end
    return (; status, reason, parameters, radius=Float64(domain), boxes, scales, min_x)
end

# Validated adaptive base lattice from a fresh level-`_ADAPTIVE_START_LEVEL` start.
# The final cells are NOT returned: a caller that keeps them keeps thousands of
# exact rational boxes alive, and no public result exposes the lattice itself.
function _adaptive_base(p; radius=nothing, max_level::Integer=16,
                        max_cells::Integer=4000, max_levels::Integer=40, max_stalls::Integer=2)
    data = _henon_data(p)
    r = _henon_radius(data, radius)
    K = Rational{BigInt}(1 + data.a_upper)
    boxes, scales, _ = _fixed_start(r, _ADAPTIVE_START_LEVEL)
    outcome = _adaptive_refine(boxes, scales, data.parameters, r, K;
                               max_level, max_cells, max_levels, max_stalls)
    return (; status=outcome.status, reason=outcome.reason, parameters=data.parameters,
            radius=outcome.radius, levels=maximum(maximum(scale) for scale in outcome.scales),
            cells=length(outcome.boxes), min_x=outcome.min_x)
end

"""
    certify_adaptive(p; radius=nothing, max_level=16, max_cells=4000, max_levels=40,
                      max_stalls=2)

Certify the base-coordinate bounded-tangent-orbit dominance test
`4*min|x|^2 > K^2` on an ADAPTIVE closed lattice of `[-r,r]^4`. The lattice keeps
an exact closed-box enclosure of the global chain recurrent set: each step drops
every cell whose image meets no remaining cell and subdivides the cells that still
fail the test, so the union of cells never loses a point of the actual set.
Returns `(status, method, reason, parameters, radius, levels, cells, min_x)` with
`status` in `:proved` / `:undetermined` / `:failed`. `:proved` means every point of
the actual global chain recurrent set satisfies the strict inequality, hence has no
nonzero bounded tangent orbit; it is NOT a claim of nonhyperbolicity for anything
else. Budget, level and refinement limits report `:undetermined`, never failure or
a counterexample. Invalid inputs, including `a=0` and uncovered radii, report
`:failed`.

The test can only succeed where the actual set stays away from the origin: the set
contains the fixed points of `H_p`, so a cell around one of them has
`min|x|` at most about `|x_fixed|` at every resolution.
"""
function certify_adaptive(p; radius=nothing, max_level::Integer=16,
                          max_cells::Integer=4000, max_levels::Integer=40, max_stalls::Integer=2)
    outcome = try
        max_level >= _ADAPTIVE_START_LEVEL && max_cells >= 16^_ADAPTIVE_START_LEVEL &&
            max_levels >= 1 || throw(ArgumentError("adaptive lattice budgets are too small"))
        _adaptive_base(p; radius, max_level, max_cells, max_levels, max_stalls)
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return (; status=:failed, method=:validation, reason=sprint(showerror, e),
                parameters=nothing, radius=nothing, levels=0, cells=0, min_x=nothing)
    end
    return (; status=outcome.status, method=:adaptive_base_dominance, reason=outcome.reason,
            parameters=outcome.parameters, radius=outcome.radius,
            levels=outcome.levels, cells=outcome.cells, min_x=outcome.min_x)
end
