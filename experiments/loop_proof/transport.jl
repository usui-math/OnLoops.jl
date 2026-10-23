# Step S5: carry the initial partition along the vertical edge c = ct + iu.
#
# Layer k holds the state boxes of parameter piece k, ordered from u = T down to
# u = 0. A continuous continuation z(u) lies in the boxes of the piece containing
# u, and at a piece boundary in the boxes of both pieces, so it stays inside one
# connected component of the "closed boxes touch" graph (within one layer and
# between consecutive layers). A label seeded at u = T therefore reaches u = 0
# only through such a component.

"""
Label masks are bit sets: `LABEL0` is symbol 0 (`Re y > 0`), `LABEL1` is
symbol 1 (`Re y < 0`).
"""
const LABEL0 = 0x01
const LABEL1 = 0x02
const NO_LABEL = 0x00
const BOTH_LABELS = LABEL0 | LABEL1

has_label0(mask) = (mask & LABEL0) != 0
has_label1(mask) = (mask & LABEL1) != 0

function require_state_box(box)
    require(length(box) == 4 && all(is_valid_interval, box),
            "state box must contain four finite guaranteed closed intervals")
end

"""
    boxes_touch(A, B)

True when the closed boxes `A` and `B` intersect (faces, edges and corners count).
"""
boxes_touch(A, B) = all(j -> inf(A[j]) <= sup(B[j]) && inf(B[j]) <= sup(A[j]), 1:4)

"""
    box_contact_index(boxes)

Search index for `foreach_box_contact`: per axis, the boxes sorted by lower
endpoint, and an upper bound of the widest box on that axis.
"""
function box_contact_index(boxes)
    require(!isempty(boxes), "cannot index an empty box collection")
    foreach(require_state_box, boxes)
    data = collect(boxes)
    lows = ntuple(j -> [inf(B[j]) for B in data], 4)
    # isless puts -0.0 before 0.0; `<` treats them as equal, as closed contact must.
    order = ntuple(j -> sortperm(lows[j]; lt=(<)), 4)
    sorted = ntuple(j -> lows[j][order[j]], 4)
    width = ntuple(j -> maximum(sup(interval(Float64, sup(B[j])) - interval(Float64, inf(B[j]))) for B in data), 4)
    require(all(isfinite, width), "box widths exceed the finite contact-index domain")
    return (; boxes=data, order, sorted, width)
end

"""
    foreach_box_contact(f, source, index; counter=Ref(0), max_candidates=100_000_000)

Call `f(i, j)` for every pair with `source[i]` touching `index.boxes[j]`.
A box `B` can touch `A` only if `inf(B_j)` lies in `[inf(A_j) - width_j, sup(A_j)]`
on every axis `j`; the axis with the fewest such candidates is scanned and each
candidate is tested with `boxes_touch`. `counter` counts the tested candidates.
"""
function foreach_box_contact(f, source, index; counter=Ref(0), max_candidates=100_000_000)
    require(0 <= counter[] <= max_candidates < typemax(Int), "invalid contact budget")
    for (i, A) in enumerate(source)
        require_state_box(A)
        ranges = ntuple(4) do j
            lowest = interval(Float64, inf(A[j])) - interval(Float64, index.width[j])
            require(!isnai(lowest) && isguaranteed(lowest), "invalid contact-query enclosure")
            (searchsortedfirst(index.sorted[j], inf(lowest); lt=(<)),
             searchsortedlast(index.sorted[j], sup(A[j]); lt=(<)))
        end
        axis = argmin(ntuple(j -> max(0, ranges[j][2] - ranges[j][1] + 1), 4))
        for position in ranges[axis][1]:ranges[axis][2]
            require(counter[] < max_candidates, "contact candidate budget exhausted; no partial result is valid")
            counter[] += 1
            j = index.order[axis][position]
            boxes_touch(A, index.boxes[j]) && f(i, j)
        end
    end
    return counter[]
end

"""
    transport_box_partitions(layers; max_vertices=2_000_000, max_candidates=100_000_000)

Label the boxes of the last layer by transporting the sign of `Re y` from the
first layer. Seeds: a first-layer box gets `LABEL0` if it meets `Re y >= 0` and
`LABEL1` if it meets `Re y <= 0`. Components of the contact graph (union-find)
take the union of their seeds. Time ends are not glued and dynamical edges are
not used.

Returns `terminal_masks` (label mask of each last-layer box) and statistics:
`components`, `collision_components` (both labels), `terminal_collisions`,
`seedless_components`, `seedless_boxes`, `vertices`, `contact_candidates`.
"""
function transport_box_partitions(layers; max_vertices=2_000_000, max_candidates=100_000_000)
    require(!isempty(layers) && all(!isempty, layers), "every closed slab requires a nonempty state cover")
    total_big = sum(big(length(layer)) for layer in layers)
    require(total_big <= max_vertices && total_big < typemax(Int), "prism vertex budget exceeded")
    foreach(layer -> foreach(require_state_box, layer), layers)
    offsets = cumsum([0; length.(layers)])
    total = Int(total_big)

    parent = collect(1:total)
    masks = fill(NO_LABEL, total)
    function root(v)
        while parent[v] != v
            parent[v] = parent[parent[v]]
            v = parent[v]
        end
        return v
    end
    function join!(a, b)
        a, b = root(a), root(b)
        a == b && return
        a, b = minmax(a, b)
        parent[b] = a
        masks[a] |= masks[b]
        masks[b] = NO_LABEL
    end

    for (i, box) in enumerate(first(layers))
        sup(box[3]) >= 0 && (masks[i] |= LABEL0)
        inf(box[3]) <= 0 && (masks[i] |= LABEL1)
    end
    require(any(has_label0, masks) && any(has_label1, masks), "initial partition misses a label")

    counter = Ref(0)
    index = box_contact_index(first(layers))
    for k in eachindex(layers)
        foreach_box_contact(layers[k], index; counter, max_candidates) do i, j
            i < j && join!(offsets[k] + i, offsets[k] + j)
        end
        if k < length(layers)
            next_index = box_contact_index(layers[k+1])
            foreach_box_contact(layers[k], next_index; counter, max_candidates) do i, j
                join!(offsets[k] + i, offsets[k+1] + j)
            end
            index = next_index
        end
    end

    roots = [root(v) for v in 1:total]
    components = unique(roots)
    terminal_masks = [masks[roots[offsets[end-1] + i]] for i in eachindex(last(layers))]
    require(any(has_label0, terminal_masks) && any(has_label1, terminal_masks),
            "transported terminal partition misses a label")
    return (; terminal_masks,
            components=length(components),
            collision_components=count(v -> masks[v] == BOTH_LABELS, components),
            terminal_collisions=count(==(BOTH_LABELS), terminal_masks),
            seedless_components=count(v -> masks[v] == NO_LABEL, components),
            seedless_boxes=count(v -> masks[v] == NO_LABEL, roots),
            vertices=total, contact_candidates=counter[])
end
