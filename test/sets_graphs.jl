import OnLoops
using OnLoops: closed_box, closed_cover, outer_graph, recurrent_vertices, graph_core, closed_intersects

@testset "Canonical closed grid geometry" begin
    grid = GAIO.BoxGrid(GAIO.Box((1.0,), (1.0,)), (2,))
    @test isequal_interval(closed_box(grid, (1,))[1], interval(0, 1))
    @test isequal_interval(closed_box(grid, (2,))[1], interval(1, 2))
    for (image, expected, escape) in ((interval(1), Set([(1,), (2,)]), false),
                                     (interval(0, 1), Set([(1,), (2,)]), false),
                                     (interval(prevfloat(1.0)), Set([(1,)]), false),
                                     (interval(nextfloat(1.0)), Set([(2,)]), false),
                                     (interval(2), Set([(2,)]), false),
                                     (interval(3, 4), Set{Tuple{Int}}(), true),
                                     (interval(-floatmax(Float64)), Set{Tuple{Int}}(), true),
                                     (interval(-1, 1), Set([(1,), (2,)]), true))
        cover = closed_cover(grid, (image,))
        @test cover.boxes.set == expected
        @test cover.may_escape == escape
    end
    for N in (2, 4)
        G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 1.0, N), ntuple(_ -> 1.0, N)), ntuple(_ -> 2, N))
        cover = closed_cover(G, ntuple(_ -> interval(1), N))
        @test length(cover.boxes) == 2^N
        @test !cover.may_escape
    end
    thirds = GAIO.BoxGrid(GAIO.Box((0.5,), (0.5,)), (3,))
    @test closed_cover(thirds, (interval(Rational{BigInt}, 1//3),)).boxes.set == Set([(1,), (2,)])
    @test closed_cover(thirds, (input_interval(1//3),)).boxes.set == Set([(1,), (2,)])
    @test closed_cover(thirds, (interval(1),)).boxes.set == Set([(3,)])
    for j in 1:3
        b = closed_box(thirds, (j,))[1]
        @test contains_exact(b, (j-1)//3) && contains_exact(b, j//3)
        @test isguaranteed(b)
    end
    tiny = nextfloat(0.0)
    tinygrid = GAIO.BoxGrid(GAIO.Box((0.0,), (tiny,)), (2,))
    @test closed_cover(tinygrid, (interval(tiny),)).boxes.set == Set([(2,)])
    @test closed_cover(tinygrid, (interval(0),)).boxes.set == Set([(1,), (2,)])
    @test contains_exact(closed_box(tinygrid, (2,))[1], Rational{BigInt}(tiny))
    for (c, r) in ((1e16, 1.0), (1e308, 1e307))
        G = GAIO.BoxGrid(GAIO.Box((c,), (r,)), (2,))
        q, s = Rational{BigInt}(c), Rational{BigInt}(r)
        @test contains_exact(closed_box(G, (1,))[1], q-s)
        @test contains_exact(closed_box(G, (2,))[1], q+s)
        @test closed_cover(G, (interval(c),)).boxes.set == Set([(1,), (2,)])
    end
    @test_throws BoundsError closed_box(grid, (0,))
    @test_throws BoundsError closed_box(grid, (3,))
    @test_throws DimensionMismatch closed_box(grid, (1, 1))
    @test_throws ArgumentError closed_box(grid, (1.0,))
    @test_throws DimensionMismatch closed_cover(grid, (interval(0), interval(0)))
    @test_throws ArgumentError closed_cover(grid, (0.0,))
    for bad in (emptyinterval(), nai(), entireinterval(), convert(Interval{Float64}, 1))
        @test_throws ArgumentError closed_cover(grid, (bad,))
    end
    for G in (GAIO.BoxGrid(GAIO.Box((0.0,), (1.0,)), (0,)),
              GAIO.BoxGrid(GAIO.Box((NaN,), (1.0,)), (2,)),
              GAIO.BoxGrid(GAIO.Box((0.0,), (NaN,)), (2,)),
              GAIO.BoxGrid(GAIO.Box((0.0,), (Inf,)), (2,)),
              GAIO.BoxGrid(GAIO.Box((floatmax(Float64),), (floatmax(Float64),)), (2,)))
        @test_throws ArgumentError closed_cover(G, (interval(0),))
    end
    @test_throws ArgumentError closed_cover(grid, (interval(1),); max_boxes=-1)
    @test_throws ArgumentError closed_cover(grid, (interval(1),); max_boxes=1)
    @test isempty(closed_cover(grid, (interval(3),); max_boxes=0).boxes)
    # Exact count must be checked before enumerating or overflowing an Int product.
    huge = GAIO.BoxGrid(GAIO.Box((0.0, 0.0), (1.0, 1.0)), (typemax(Int), typemax(Int)))
    @test_throws ArgumentError closed_cover(huge, (interval(-1, 1), interval(-1, 1)); max_boxes=100)
    @test length(closed_cover(huge, (interval(0), interval(0))).boxes) == 1
end

@testset "Exact closed-cover oracle" begin
    for n in (1, 2, 3, 5)
        G = GAIO.BoxGrid(GAIO.Box((1.5,), (2.5,)), (n,))  # exact domain [-1,4]
        for i in -4:10, j in i:10
            lo, hi = big(i)//2, big(j)//2
            expected = Set((k,) for k in 1:n if -1 + (k-1)*(5//n) <= hi && lo <= -1 + k*(5//n))
            cover = closed_cover(G, (interval(Rational{BigInt}, lo, hi),))
            @test cover.boxes.set == expected
            @test cover.may_escape == (lo < -1 || hi > 4)
        end
    end
    for (T, I) in ((Float32, Int32), (Float64, UInt8))
        G = GAIO.BoxGrid(GAIO.Box{1,T}((1,), (1,)), (I(2),))
        @test closed_cover(G, (interval(T, 1),)).boxes.set == Set([(I(1),), (I(2),)])
        @test all(isguaranteed, closed_box(G, (I(2),)))
    end
end

@testset "Chunked graph build matches the exact per-cell reference" begin
    p = map(input_interval, (1, 0, -10, 0))
    r = OnLoops.henon_radius(p)
    G = GAIO.BoxGrid(GAIO.Box((0.0, 0.0, 0.0, 0.0), (r, r, r, r)), (8, 8, 8, 8))
    source = GAIO.cover(G, :)
    f = z -> henon(z, p)
    g = outer_graph(f, source; max_edges=8_000_000)
    keys = sort!(collect(source.set))
    @test length(keys) == 4096
    @test g.keys == keys
    @test all(issorted, g.adjacency)
    index = Dict(key => u for (u, key) in enumerate(keys))
    for (u, key) in enumerate(keys)
        hit = closed_cover(G, f(closed_box(G, key)))
        expected = sort!([index[t] for t in hit.boxes.set if haskey(index, t)])
        @test g.adjacency[u] == expected
        @test g.may_escape[u] == hit.may_escape
        @test g.may_leave[u] == (hit.may_escape || !all(haskey(index, t) for t in hit.boxes.set))
    end
    repeat = outer_graph(f, source; max_edges=8_000_000)
    @test repeat.keys == g.keys && repeat.adjacency == g.adjacency
    @test repeat.may_escape == g.may_escape && repeat.may_leave == g.may_leave
    @test_throws ArgumentError outer_graph(f, source; max_edges=sum(length.(g.adjacency)) - 1)
end

@testset "Cached cell boundaries equal the exact rational cells" begin
    # Adversarial domains: non-dyadic thirds, cancellation, subnormal width and
    # very large magnitudes. Every cell of every grid must match exactly.
    domains = ((1.5, 2.5), (1//3, 1//3), (1e16, 1.0), (1e-320, 1e-321), (1e300, 1e299))
    for (center, radius) in domains, n in (1, 2, 3, 5, 8)
        for T in (Float64, Float32)
            c, r = T(center), T(radius)
            # Skip domains a narrower type cannot even represent.
            isfinite(c) && isfinite(r) && r > 0 || continue
            grid = GAIO.BoxGrid(GAIO.Box{1,T}((c,), (r,)), (n,))
            geometry = OnLoops._grid_geometry(grid)
            bounds = OnLoops._cell_bounds(geometry, T)
            for j in 1:n
                @test isequal_interval(OnLoops._cached_box(bounds, (j,), T)[1],
                                       OnLoops._closed_box(geometry, (j,), T)[1])
            end
        end
    end
    # Two- and four-dimensional grids, including the upper boundary cell.
    for dims in ((3, 4), (3, 3, 3, 3))
        grid = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.25, length(dims)), ntuple(_ -> 1.75, length(dims))), dims)
        geometry = OnLoops._grid_geometry(grid)
        bounds = OnLoops._cell_bounds(geometry, Float64)
        for key in Iterators.product(ntuple(k -> 1:dims[k], length(dims))...)
            @test all(isequal_interval(a, b) for (a, b) in
                      zip(OnLoops._cached_box(bounds, key, Float64),
                          OnLoops._closed_box(geometry, key, Float64)))
        end
    end
end

@testset "Fast index ranges equal the exact rational ranges" begin
    # Reference is the Rational{BigInt} closed-cover formula; the fast path may
    # only be used when it returns exactly the same cell set.
    function check_cover(grid, image)
        geometry = OnLoops._grid_geometry(grid)
        bounds = OnLoops._cell_bounds(geometry, eltype(typeof(grid.domain)))
        exact = OnLoops._closed_cover(grid, geometry, image, 10^9)
        fast = OnLoops._closed_cover(grid, geometry, bounds, image, 10^9)
        @test fast.boxes.set == exact.boxes.set
        @test fast.may_escape == exact.may_escape
    end
    for (center, radius, sizes) in ((1.0, 1.0, (1, 2, 3, 5, 7, 16)),
                                    (1//3, 1//3, (1, 3, 8)),
                                    (1e16, 1.0, (2, 4)),
                                    (1e-320, 1e-321, (2, 3)),
                                    (1e300, 1e299, (2, 5)))
        for n in sizes
            grid = GAIO.BoxGrid(GAIO.Box{1,Float64}((Float64(center),), (Float64(radius),)), (n,))
            geometry = OnLoops._grid_geometry(grid)
            L = geometry.lower[1]
            h = geometry.step[1]
            for i in 0:n
                b = L + i*h
                # Exact boundaries, one ulp to either side, and the midpoint.
                for value in (b, b - h//4, b + h//4)
                    check_cover(grid, (interval(Float64, value, value),))
                end
                check_cover(grid, (interval(Float64, prevfloat(Float64(b)), b),))
                check_cover(grid, (interval(Float64, b, nextfloat(Float64(b))),))
            end
            check_cover(grid, (interval(Float64, L - 2, L + 2),))              # partial escape
            check_cover(grid, (interval(Float64, L + n*h + 1, L + n*h + 2),))  # fully outside
            check_cover(grid, (interval(Float64, L - 3, L - 2),))
            check_cover(grid, (interval(Float64, -1e308, 1e308),))             # contains everything
        end
    end
    # Multi-dimensional grids, including 8 coordinates for the tangent lattice.
    for dims in ((2, 3), (2, 2, 2, 2), (2, 2, 3, 2, 2, 2, 3, 2))
        grid = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.25, length(dims)), ntuple(_ -> 1.75, length(dims))), dims)
        geometry = OnLoops._grid_geometry(grid)
        for axis in 1:length(dims)
            n = dims[axis]
            for i in 0:n
                b = geometry.lower[axis] + i*geometry.step[axis]
                for value in (b, b + geometry.step[axis]//4)
                    image = ntuple(k -> k == axis ? interval(Float64, value, value) :
                                               interval(Float64, -2, 2), length(dims))
                    check_cover(grid, image)
                end
            end
        end
        check_cover(grid, ntuple(_ -> interval(Float64, -3, 3), length(dims)))
        check_cover(grid, ntuple(_ -> interval(Float64, 1//3, 1//2), length(dims)))
    end
end

@testset "Closed collisions are not key intersection" begin
    G = GAIO.BoxGrid(GAIO.Box((1.5, 1.5), (1.5, 1.5)), (3, 3))
    A = GAIO.BoxSet(G, Set([(1, 1)]))
    B = GAIO.BoxSet(G, Set([(2, 2)]))
    C = GAIO.BoxSet(G, Set([(3, 3)]))
    @test isdisjoint(A, B)
    @test closed_intersects(A, B)
    @test closed_intersects(B, A)
    @test !closed_intersects(A, C)
    @test closed_intersects(A, A)
    @test !closed_intersects(A, GAIO.BoxSet(G))
    @test_throws ArgumentError closed_intersects(A, GAIO.BoxSet(GAIO.subdivide(G, 1)))
    @test_throws BoundsError closed_intersects(A, GAIO.BoxSet(G, Set([(0, 1)])))
end

@testset "Boolean full-box graph" begin
    G = GAIO.BoxGrid(GAIO.Box((1.0,), (1.0,)), (2,))
    source = GAIO.BoxSet(G, Set([(2,), (1,)]))
    before = copy(source.set)
    g = outer_graph(_ -> (interval(1),), source)
    @test g.keys == [(1,), (2,)]
    @test g.adjacency == [[1, 2], [1, 2]]
    @test !any(g.may_escape) && !any(g.may_leave)
    @test recurrent_vertices(g.adjacency) == [1, 2]
    @test graph_core(g.adjacency) == [1, 2]
    @test source.set == before
    onecell = GAIO.BoxSet(G, Set([(1,)]))
    identity_graph = outer_graph(identity, onecell)
    @test identity_graph.adjacency == [[1]]
    @test identity_graph.may_escape == [false]
    @test identity_graph.may_leave == [true]  # conservative boundary-neighbour hit
    escaped = outer_graph(_ -> (interval(3),), source)
    @test escaped.adjacency == [Int[], Int[]]
    @test all(escaped.may_escape) && all(escaped.may_leave)
    @test isempty(graph_core(escaped.adjacency))
    @test isempty(outer_graph(identity, GAIO.BoxSet(G)).adjacency)
    @test_throws ArgumentError outer_graph(identity, source; max_vertices=1)
    @test_throws ArgumentError outer_graph(identity, source; max_vertices=-1)
    @test_throws ArgumentError outer_graph(identity, source; max_edges=3)
    @test_throws ArgumentError outer_graph(identity, source; max_edges=-1)
    @test_throws ArgumentError outer_graph(_ -> (0.5,), source)
    @test_throws ArgumentError outer_graph(_ -> (nai(),), source)
    @test_throws DimensionMismatch outer_graph(_ -> (interval(0), interval(0)), source)
    @test_throws BoundsError outer_graph(identity, GAIO.BoxSet(G, Set([(0,)])))
end

@testset "Hénon graph includes exact complex parameter images" begin
    G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> 1.0, 4)), (2, 2, 2, 2))
    source = GAIO.cover(G, :)
    bounds = ((1//4, 1//2), (-1//8, 1//8), (-3//4, 1//4), (-1//4, 1//4))
    p = map(b -> interval(Float64, b...), bounds)
    g = outer_graph(z -> henon(z, p), source)
    parameters = vec([Tuple(t) for t in Iterators.product(bounds...)])
    push!(parameters, map(b -> (b[1]+b[2])/2, bounds))
    for (u, key) in enumerate(g.keys)
        state_bounds = map(j -> ((j-2)//1, (j-1)//1), key)
        states = vec([Tuple(t) for t in Iterators.product(state_bounds...)])
        push!(states, map(b -> (b[1]+b[2])/2, state_bounds))
        for z in states, parameter in parameters
            x, y = complex(z[1], z[2]), complex(z[3], z[4])
            a, c = complex(parameter[1], parameter[2]), complex(parameter[3], parameter[4])
            X = x^2 + c - a*y
            exact = (real(X), imag(X), real(x), imag(x))
            if all(q -> -1 <= q <= 1, exact)
                # Independent closed-cell oracle, including ALL boundary neighbours.
                expected = [v for (v, target) in enumerate(g.keys)
                            if all(target[k]-2 <= exact[k] <= target[k]-1 for k in 1:4)]
                @test !isempty(expected) && all(v -> v in g.adjacency[u], expected)
            else
                @test g.may_escape[u]
            end
        end
    end
end

# Small independent oracles: positive-length reachability and fixed-point deletion.
function recurrent_oracle(adjacency)
    n = length(adjacency)
    reachable = falses(n, n)
    for u in 1:n, v in adjacency[u]
        reachable[u, v] = true
    end
    for k in 1:n, u in 1:n, v in 1:n
        reachable[u, v] |= reachable[u, k] && reachable[k, v]
    end
    return [u for u in 1:n if reachable[u, u]]
end

function core_oracle(adjacency)
    alive = Set(1:length(adjacency))
    while true
        next = Set(u for u in alive if any(v -> v in alive, adjacency[u]) &&
                   any(v -> u in adjacency[v], alive))
        next == alive && return sort!(collect(alive))
        alive = next
    end
end

@testset "Recurrence and bi-infinite graph core are distinct" begin
    @test recurrent_vertices([Int[]]) == Int[]
    @test graph_core([Int[]]) == Int[]
    @test recurrent_vertices([[1]]) == [1]
    @test graph_core([[1]]) == [1]
    @test recurrent_vertices([[2], [1]]) == [1, 2]
    @test graph_core([[2], [1]]) == [1, 2]
    bridge = [[1, 2], [3], [3]]
    @test recurrent_vertices(bridge) == [1, 3]
    @test graph_core(bridge) == [1, 2, 3]
    @test recurrent_vertices([[2], [3], Int[]]) == Int[]
    @test graph_core([[2], [3], Int[]]) == Int[]
    @test recurrent_vertices([[1, 1]]) == [1]
    @test graph_core([[1, 1]]) == [1]
    @test isempty(recurrent_vertices(Vector{Int}[]))
    @test isempty(graph_core(Vector{Int}[]))
    for mask in 0:2^9-1
        adjacency = [[v for v in 1:3 if (mask >> ((u-1)*3+v-1)) & 1 == 1] for u in 1:3]
        before = deepcopy(adjacency)
        @test recurrent_vertices(adjacency) == recurrent_oracle(adjacency)
        @test graph_core(adjacency) == core_oracle(adjacency)
        @test adjacency == before
    end
    for f in (recurrent_vertices, graph_core), bad in ([[0]], [[2]], [[-1]], [[1.0]])
        @test_throws ArgumentError f(bad)
    end
    # Long paths/cycles must not overflow a recursive DFS stack.
    n = 20_000
    chain = [[u+1] for u in 1:n-1]
    push!(chain, Int[])
    @test isempty(recurrent_vertices(chain))
    @test isempty(graph_core(chain))
    chain[end] = [1]
    @test recurrent_vertices(chain) == collect(1:n)
    @test graph_core(chain) == collect(1:n)
end
