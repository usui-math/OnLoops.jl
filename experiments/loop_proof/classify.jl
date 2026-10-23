# Step S6: the action rho on a finite symbolic window, read at the midpoint.
#
# A_b is the partition of K carried from the basepoint to the midpoint by the
# upper half of the loop, and C is complex conjugation of the state. For the
# conjugate-symmetric loop rho = h C h^{-1} with h = h_0 T_alpha^{-1}, so
# rho(s)_0 = b exactly when the midpoint point coded by s lies in C(A_b).
# The window [-memory, anticipation] cylinder of a word w is enclosed by the
# time-0 boxes of graph paths whose boxes touch A-hat_{w_i} at every position i.
# The output is b only when that enclosure misses C(A-hat_{1-b}).

conjugate_state_box(B) = (B[1], -B[2], B[3], -B[4])

"""
    box_label_masks(boxes, A0, A1; counter=Ref(0), max_candidates=100_000_000)

For every box, the mask of the label enclosures it touches: `LABEL0` if it
touches a box of `A0`, `LABEL1` if it touches a box of `A1`.
"""
function box_label_masks(boxes, A0, A1; counter=Ref(0), max_candidates=100_000_000)
    require(!isempty(A0) && !isempty(A1), "both transported label enclosures must be nonempty")
    masks = fill(NO_LABEL, length(boxes))
    foreach_box_contact(boxes, box_contact_index(A0); counter, max_candidates) do i, _
        masks[i] |= LABEL0
    end
    foreach_box_contact(boxes, box_contact_index(A1); counter, max_candidates) do i, _
        masks[i] |= LABEL1
    end
    return masks
end

"""
    all_words(L)

All `2^L` binary words of length `L` in lexicographic order.
"""
all_words(L) = [ntuple(j -> (bits >> (L - j)) & 1, L) for bits in 0:2^L-1]

"""
    word_output(cylinder, output_masks)

`:label0` / `:label1` when the cylinder boxes touch only `C(A0)` / only `C(A1)`,
`:undetermined` when they touch both, `:inconsistent` when the cylinder is
empty or touches neither (impossible for a true full two-shift).
"""
function word_output(cylinder, output_masks)
    contact = foldl(|, (output_masks[v] for v in cylinder); init=NO_LABEL)
    output = isempty(cylinder) || contact == NO_LABEL ? :inconsistent :
             contact == BOTH_LABELS ? :undetermined :
             contact == LABEL0 ? :label0 : :label1
    return (; contact0=has_label0(contact), contact1=has_label1(contact), output)
end

"""
    classify_midpoint_rule(boxes, edges, A0, A1; memory=1, anticipation=2,
                           max_words=1024, max_candidates=100_000_000)

Classify every word on the window `-memory, ..., 0, ..., anticipation`.
`boxes` and `edges` are the midpoint enclosure, `A0` and `A1` the transported
label enclosures. Boxes touching neither `A0 ∪ A1` nor its conjugate carry no
point of K and are removed before taking the `graph_core`. Returns `status`
(`:determined`, `:undetermined` or `:failed`), the `table` of
`(word, boxes, contact0, contact1, output)` rows and statistics.
"""
function classify_midpoint_rule(boxes, edges, A0, A1; memory=1, anticipation=2,
                                max_words=1024, max_candidates=100_000_000)
    require(memory isa Integer && anticipation isa Integer && memory >= 0 && anticipation >= 0,
            "symbol window must be nonnegative")
    L = big(memory) + big(anticipation) + 1
    require(L <= 62, "symbolic window is too large to enumerate exactly")
    require(big(2)^Int(L) <= max_words, "word budget exceeded")
    L, m, n = Int(L), Int(memory), Int(anticipation)
    vertices = length(boxes)
    require(vertices > 0, "empty target state cover")
    require(all(e -> all(v -> 1 <= v <= vertices, e), edges), "target edge index outside cover")

    counter = Ref(0)
    input_masks = box_label_masks(boxes, A0, A1; counter, max_candidates)
    output_masks = box_label_masks(boxes, conjugate_state_box.(A0), conjugate_state_box.(A1);
                                   counter, max_candidates)

    adjacency = [Int[] for _ in 1:vertices]
    for (v, w) in edges
        push!(adjacency[v], w)
    end
    supported = [input_masks[v] != NO_LABEL && output_masks[v] != NO_LABEL for v in 1:vertices]
    adjacency = [supported[v] ? [w for w in adjacency[v] if supported[w]] : Int[] for v in 1:vertices]
    retained = fill(false, vertices)
    retained[graph_core(adjacency)] .= true
    adjacency = [retained[v] ? [w for w in adjacency[v] if retained[w]] : Int[] for v in 1:vertices]
    incoming = OnLoops._reverse_graph(adjacency)
    labels = [(retained[v] && has_label0(input_masks[v]), retained[v] && has_label1(input_masks[v]))
              for v in 1:vertices]

    table = map(all_words(L)) do word
        cylinder = OnLoops._cylinder_indices(adjacency, incoming, labels, m, n, word)
        merge((; word, boxes=length(cylinder)), word_output(cylinder, output_masks))
    end
    status = any(row -> row.output == :inconsistent, table) ? :failed :
             any(row -> row.output == :undetermined, table) ? :undetermined : :determined
    return (; status, table, memory=m, anticipation=n,
            retained_vertices=count(retained),
            input_overlap=count(==(BOTH_LABELS), input_masks),
            input_unlabelled=count(==(NO_LABEL), input_masks),
            output_overlap=count(==(BOTH_LABELS), output_masks),
            contact_candidates=counter[])
end
