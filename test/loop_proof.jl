# Regression checks for experiments/loop_proof (steps S0-S7 of the symmetric-loop proof).
# They do not replace the full `prove` runs.
include("../experiments/certify_symmetric_loops.jl")

function refuses(action)
    try
        action()
    catch err
        err isa ArgumentError || rethrow()
        return true
    end
    return false
end

point_box(z) = map(input_interval, z)
contains_point(box, z) = all(j -> Q(inf(box[j])) <= z[j] <= Q(sup(box[j])), 1:4)

function refine_check()
    parents = Set([(1, 1, 1, 1), (2, 1, 1, 1)])
    kids = refine(parents)
    @assert length(kids) == 16length(parents)
    @assert Set(ntuple(j -> (k[j] + 1) ÷ 2, 4) for k in kids) == parents
    @assert refine(Set(Iterators.product(1:2, 1:2, 1:2, 1:2))) == Set(Iterators.product(1:4, 1:4, 1:4, 1:4))
    println("PASS: refine gives exactly the 16 children of each cell.")
end

function henon_inverse_check()
    p = (Q(-19, 40), Q(0), Q(-7, 4), Q(0))
    z = (Q(-1, 3), Q(1, 5), Q(2, 7), Q(-3, 11))
    w = henon(z, p)
    @assert henon_inverse(w, p) == z && henon(henon_inverse(w, p), p) == w
    @assert contains_point(henon_inverse(point_box(w), point_box(p)), z)
    println("PASS: henon_inverse inverts henon exactly and its interval image contains the preimage.")
end

function shrink_edge_check()
    p_exact = (Q(-19, 40), Q(0), Q(-7, 4), Q(0))
    p = point_box(p_exact)
    for z in ((Q(1, 3), Q(1, 5), Q(-2, 7), Q(3, 11)), (Q(1), Q(0), Q(0), Q(0)), (Q(-1), Q(0), Q(0), Q(0)), (Q(0), Q(0), Q(1), Q(0)))
        w = henon(z, p_exact)
        for width in (Q(0), Q(1, 10))
            around(point) = map(q -> interval(Float64, q - width, q + width), point)
            pair = shrink_edge(around(z), around(w), p)
            @assert !isnothing(pair) && contains_point(pair[1], z) && contains_point(pair[2], w)
        end
    end
    source = map(q -> interval(Float64, q[1], q[2]), ((2//1, 21//10), (0//1, 0//1), (0//1, 1//10), (0//1, 0//1)))
    target = map(q -> interval(Float64, q[1], q[2]), ((-2//1, -19//10), (0//1, 0//1), (2//1, 21//10), (0//1, 0//1)))
    @assert isnothing(shrink_edge(source, target, p))
    one = point_box((1, 0, 0, 0))
    unguaranteed = p[1] + 0.0
    @assert !isguaranteed(unguaranteed)
    @assert refuses(() -> shrink_edge(one, one, (unguaranteed, p[2], p[3], p[4])))
    @assert refuses(() -> shrink_edge(one, one, (nai(Float64), p[2], p[3], p[4])))
    println("PASS: shrink_edge keeps exact pairs, removes an impossible edge, refuses NaI and unguaranteed input.")
end

function cone_controls_check()
    diagonal_forms(cover, a) = fill((Q(1), Q(0), Q(0), -abs(a)), length(cover.cells))
    dn = shrink_cover(global_cover(point_box((1//4, 0, -10, 0)); max_level=4); passes=5)
    @assert exact_cone_margin(dn, diagonal_forms(dn, Q(1, 4))) > 0
    unit = shrink_cover(global_cover(point_box((1, 0, 0, 0)); max_level=3); passes=5)
    zero_cells = Set(i for (i, B) in enumerate(unit.boxes) if all(I -> inf(I) <= 0 <= sup(I), B))
    @assert length(zero_cells) == 16
    zero_loops = count(eachindex(unit.edges)) do e
        k, j = unit.edges[e]
        x = unit.edge_x_boxes[e]
        k == j && k in zero_cells && x[1] <= 0 <= x[2] && x[3] <= 0 <= x[4]
    end
    @assert zero_loops == 16 && exact_cone_margin(unit, diagonal_forms(unit, Q(1))) <= 0
    println("PASS: DN control has a positive exact margin; H_{1,0} keeps its 16 neutral zero self-loops and is refused.")
end

function cone_forms_file_check()
    dir = mktempdir()
    path = joinpath(dir, "forms-roundtrip.tsv")
    cells = [(1, 2, 3, 4), (128, 1, 64, 2), (5, 5, 5, 5)]
    forms = [(Q(-3, 7), Q(big(2)^80 + 1, 3), Q(0), Q(5)), (Q(1, 2^60), Q(-1), Q(2, 3), Q(-big(10)^30, 7)), (Q(0), Q(0), Q(0), Q(0))]
    write_cone_forms(path, cells, forms)
    @assert all(line -> !occursin("//", line), readlines(path))
    @assert read_cone_forms(path, reverse(cells)) == reverse(forms)
    @assert isnothing(read_cone_forms(path, [(9, 9, 9, 9)]))
    @assert isnothing(read_cone_forms(path * ".missing", cells))
    write(path, read(path, String) * "1\t2\t3\t4\t1/1\t0/1\t0/1\t1/1\n")
    @assert refuses(() -> read_cone_forms(path, cells))
    rm(dir; recursive=true)
    println("PASS: exact p/q form text round trip, reordered cells, missing cell or file gives no forms, duplicate cell refused.")
end

function transport_check()
    I(a, b=a) = interval(Float64, a, b)
    X(a, b) = (I(a, b), I(0), I(0), I(0))
    Y(a, b, u, v) = (I(0), I(0), I(a, b), I(u, v))
    exact_touch(A, B) = all(j -> Q(inf(A[j])) <= Q(sup(B[j])) && Q(inf(B[j])) <= Q(sup(A[j])), 1:4)
    a = [X(0, 1), X(1, 2), X(3, 4), X(1, 1), X(prevfloat(1.0), 1.0), X(-0.0, -0.0)]
    b = [X(1, 1), X(2, 3), X(4, 5), X(-2, -1), X(1//2, 3//4), X(1.0, nextfloat(1.0)), X(0.0, 0.0)]
    found = Set{Tuple{Int,Int}}()
    foreach_box_contact((i, j) -> push!(found, (i, j)), a, box_contact_index(b))
    @assert found == Set((i, j) for i in eachindex(a) for j in eachindex(b) if exact_touch(a[i], b[j]))
    @assert (1, 1) in found && (2, 2) in found && (3, 3) in found && (4, 1) in found

    layers = [[Y(-2, -1, 0, 1), Y(1, 2, -1, 0)], [Y(-1, 1, 1, 1), Y(-1, 1, -1, -1)], [Y(1, 2, 0, 1), Y(-2, -1, -1, 0)]]
    transport = transport_box_partitions(layers)
    @assert transport.terminal_masks == [LABEL1, LABEL0]
    @assert transport.collision_components == 0 && transport.seedless_components == 0
    collision = transport_box_partitions([[Y(-1, 1, 0, 0)], [Y(-1, 1, 0, 0)]])
    @assert collision.terminal_masks == [BOTH_LABELS] && collision.collision_components == 1

    @assert refuses(() -> foreach_box_contact((i, j) -> nothing, a, box_contact_index(b); max_candidates=0))
    @assert refuses(() -> box_contact_index([(nai(Float64), I(0), I(0), I(0))]))
    @assert refuses(() -> box_contact_index([(I(0) + 0.0, I(0), I(0), I(0))]))
    println("PASS: closed face/corner/signed-zero contacts, labels transported (not reset at the end), collisions kept, invalid data and budgets refused.")
end

function classify_check()
    I(a) = interval(Float64, a)
    Y(a, b) = (I(0), I(0), I(a), I(b))
    points = [Y(-1, 0), Y(1, 0)]
    all_edges = [(i, j) for i in 1:2 for j in 1:2]
    table = classify_midpoint_rule(points, all_edges, [points[1]], [points[2]]; memory=1, anticipation=2).table
    @assert length(table) == 16 && all(row -> row.output == (row.word[2] == 0 ? :label0 : :label1), table)
    both = (I(0), I(0), interval(Float64, -1, 1), I(0))
    @assert all(row -> row.output == :undetermined, classify_midpoint_rule(points, all_edges, [both], [both]; memory=0, anticipation=0).table)
    for (m, n) in ((1, 1), (0, 0))
        no_paths = classify_midpoint_rule(points, Tuple{Int,Int}[], [points[1]], [points[2]]; memory=m, anticipation=n)
        @assert all(row -> row.output == :inconsistent, no_paths.table) && no_paths.status == :failed
    end
    off_axis = [(I(0), I(0), I(-1), I(1)), (I(0), I(0), I(1), I(1))]
    @assert all(row -> row.output == :inconsistent, classify_midpoint_rule(off_axis, all_edges, [off_axis[1]], [off_axis[2]]; memory=0, anticipation=0).table)
    @assert refuses(() -> classify_midpoint_rule(points, all_edges, [points[1]], [points[2]]; memory=big(typemax(Int)), anticipation=0))
    @assert refuses(() -> classify_midpoint_rule(points, all_edges, [points[1]], empty(points); memory=0, anticipation=0))

    dn = shrink_cover(global_cover(point_box((1//4, 0, -11, 0)); max_level=4); passes=5)
    @assert dn.radius == 4 && any(B -> contains_point(B, (4, 0, 4, 0)), dn.boxes)
    A0 = [B for B in dn.boxes if sup(B[3]) >= 0]
    A1 = [B for B in dn.boxes if inf(B[3]) <= 0]
    identity = classify_midpoint_rule(dn.boxes, dn.edges, A0, A1; memory=2, anticipation=4)
    @assert identity.status == :determined && length(identity.table) == 128
    @assert all(row -> row.output == (row.word[3] == 0 ? :label0 : :label1), identity.table)
    dir = mktempdir()
    zero_forms = joinpath(dir, "zero-forms.tsv")
    write_cone_forms(zero_forms, dn.cells, fill((Q(0), Q(0), Q(0), Q(0)), length(dn.cells)))
    @assert exact_cone_margin(dn, read_cone_forms(zero_forms, dn.cells)) == 0
    rm(dir; recursive=true)
    println("PASS: opposite-label exclusion, unresolved and inconsistent words, 128 identity words at a DN point, stored zero forms rechecked and not accepted.")
end

"""The rule found for (-19/40, -7/4) on the window -2..4."""
function minus19_40_bit(w)
    flip = (w[2], w[4], w[5]) == (0, 1, 0) || (w[1], w[2], w[4], w[5], w[6], w[7]) == (1, 0, 1, 1, 1, 0)
    return flip ? 1 - w[3] : w[3]
end

function rule_check()
    known = Dict(w => minus19_40_bit(w) for w in Iterators.product(ntuple(_ -> 0:1, 7)...))
    @assert involution_check(known, 2, 4)
    @assert minimal_windows(known, 2, 4) == [(-2, 4)]
    fixed_points = map(1:8) do n
        count(0:2^n-1) do bits
            s(j) = (bits >> (n - mod1(j, n))) & 1
            all(i -> apply_rule(known, 2, 4, s, i) == s(i), 1:n)
        end
    end
    @assert fixed_points == [2, 4, 2, 8, 2, 28, 30, 80]
    shift = Dict(w => w[1] for w in Iterators.product(ntuple(_ -> 0:1, 3)...))
    @assert !involution_check(shift, 1, 1)
    @assert minimal_windows(shift, 1, 1) == [(-1, -1)]
    @assert refuses(() -> rule_from_table([(word=(0,), output=:undetermined)]))
    println("PASS: the -19/40 rule is an involution with minimal window [-2,4] and known periodic counts; the shift is not an involution.")
end

function loop_check()
    for spec in values(LOOP_SPECS)
        loop = symmetric_loop(spec)
        @assert loop.times[4] == 1//2 && loop.points[4] == (spec.a, 0, spec.ct, 0)
        require_contiguous(initial_pieces(spec.T), spec.T)
    end
    neg = symmetric_loop(LOOP_SPECS["a-19_40_c-7_4"])
    @assert neg.points[1:4] == [(Q(-19, 40), 0, c...) for c in ((-6, 0), (-6, 4), (-7//4, 4), (-7//4, 0))]
    pieces = initial_pieces(Q(4))
    @assert length(pieces) == 120 && count(p -> p[3] == 7, pieces) == 16 && all(p -> (p[3] == 7) == (p[2] <= Q(1, 8)), pieces)
    @assert refuses(() -> symmetric_loop((a=Q(-1), c0=Q(-9), ct=Q(-7, 2), T=Q(29, 4))))
    @assert refuses(() -> symmetric_loop((a=Q(-1), c0=Q(-10), ct=Q(-7, 2), T=Q(7))))
    @assert refuses(() -> require_contiguous([(Q(0), Q(1), 6), (Q(2), Q(3), 6)], Q(3)))
    println("PASS: exact loop gates (DN, HOV on left/top edges, conjugate symmetry) and contiguous pieces.")
end

refine_check()
henon_inverse_check()
shrink_edge_check()
cone_controls_check()
cone_forms_file_check()
transport_check()
classify_check()
rule_check()
loop_check()
