import OnLoops
using OnLoops: RationalLoop, loop_box, certify_monodromy, beta, gamma, BETA_LOOP, GAMMA_LOOP,
               report_monodromy, monodromy_markdown,
               _dn_gate, _cylinder_indices, _classify_cylinder, _keys_contact

const CONSTANT_DN = RationalLoop((0, 1), ((1, 0, -10, 0), (1, 0, -10, 0)))
const SMALL_HOV = RationalLoop((0, 1//3, 2//3, 1),
    ((1, 0, -10, 0), (1, 0, -10, 1//16), (1, 0, -10+1//16, 1//16), (1, 0, -10, 0)))

@testset "Exact rational loop data" begin
    for loop in (BETA_LOOP, GAMMA_LOOP)
        @test loop.times[1] == 0 && loop.times[end] == 1
        @test loop.points[1] == loop.points[end]
        @test all(loop.times[j] < loop.times[j+1] for j in 1:length(loop.times)-1)
        @test eltype(loop.points) === NTuple{4,Rational{BigInt}}
    end
    # Independent exact reference inside one linear segment: on t in [1/8,3/8] of
    # the gamma segment from c=-10 to c=-11/4, c is exactly [-211/24,-95/24].
    box = loop_box(GAMMA_LOOP, interval(Float64, 1//8, 3//8))
    @test box[1] == interval(Float64, 1//4) && box[2] == interval(Float64, 0) && box[4] == interval(Float64, 0)
    @test inf(box[3]) <= -211//24 && sup(box[3]) >= -95//24
    # Exact image width is 145/24 - 29/24 = 29/6; the enclosure adds only rounding.
    @test sup(box[3]) - inf(box[3]) <= 29//6 + 1e-12
    # Fold crossing must include the exact fold value at t = 29/64.
    fold = loop_box(GAMMA_LOOP, interval(Float64, 29//64 - 1//1024, 29//64 + 1//1024))
    @test inf(fold[3]) <= -11//4 <= sup(fold[3])
    @test inf(fold[4]) <= -1//4 <= sup(fold[4])
    t = interval(Float64, 0, 1)
    @test all(isequal_interval.(loop_box(GAMMA_LOOP, t), gamma(t)))
    t = interval(Float64, 1//4, 1//2)
    @test all(isequal_interval.(loop_box(BETA_LOOP, t), beta(t)))
    @test_throws ArgumentError loop_box(GAMMA_LOOP, interval(Float64, 1//2, 2))
    @test_throws ArgumentError RationalLoop((0, 1), ((1, 0, -10, 0), (1, 0, -9, 0)))
    @test_throws ArgumentError RationalLoop((0, 1//2), ((1, 0, -10, 0), (1, 0, -10, 0)))
    @test_throws ArgumentError RationalLoop((1, 0), ((1, 0, -10, 0), (1, 0, -10, 0)))
    @test_throws ArgumentError RationalLoop((0, 1//2, 1//2, 1),
        ((1,0,-10,0), (1,0,-10,0), (1,0,-10,0), (1,0,-10,0)))
    @test_throws ArgumentError RationalLoop((0, 1), ((1, 0, -10, 0),))
    @test_throws ArgumentError RationalLoop((0, 1), ((1, 0, -10, 0), (1, 0)))
end

@testset "Horseshoe gate validates the exact path" begin
    @test OnLoops._loop_geometry_check(GAMMA_LOOP) == (1, 0, -10, 0)
    @test_throws ArgumentError OnLoops._loop_geometry_check(BETA_LOOP)  # base is not in DN
    rejected = certify_monodromy(BETA_LOOP)
    @test rejected.status == :failed
    @test occursin("Devaney-Nitecki", rejected.reason)
    @test isnothing(rejected.partitions)
    # |a| <= 1 is checked at vertices; a linear image stays in the convex disk.
    outside = RationalLoop((0, 1//2, 1), ((1, 0, -10, 0), (2, 1, -10, 0), (1, 0, -10, 0)))
    @test certify_monodromy(outside).status == :failed
    singular = RationalLoop((0, 1), ((0, 0, -10, 0), (0, 0, -10, 0)))
    @test certify_monodromy(singular).status == :failed
    imaginary = RationalLoop((0, 1), ((1, 1//2, -10, 0), (1, 1//2, -10, 0)))
    @test certify_monodromy(imaginary).status == :failed
end

@testset "Slab certificates and labelled partition enclosures" begin
    # y = 0 must be a grid boundary, so every state partition axis is even.
    for kwargs in ((; dims=(3,3,3,3)), (; dims=(0,2,2,2)), (; dims=(2,2,2)), (; dims=-2), (; slabs=0),
                   (; max_refinements=-1), (; max_vertices=-1), (; max_edges=-1))
        @test certify_monodromy(CONSTANT_DN; kwargs...).status == :failed
    end
    coarse = certify_monodromy(CONSTANT_DN; slabs=2, dims=4, max_refinements=0)
    @test coarse.status == :undetermined
    @test coarse.collision
    @test occursin("refinement cap", coarse.reason)
    @test !isnothing(coarse.partitions)
    # Resolution decides separation: 16 cells per state axis separate, 4 do not.
    fine = certify_monodromy(CONSTANT_DN; slabs=1, dims=16, max_refinements=0, max_edges=8_000_000)
    @test fine.status == :proved
    @test !fine.collision
    @test 4.3166 < fine.radius < 4.3167
    @test fine.components == 4
    label0, label1 = only(fine.partitions)
    @test !isempty(label0) && !isempty(label1)
    @test isempty(intersect(label0, label1))
    @test length(label0) + length(label1) == 658
    # The initial partition is exactly the two DN half-planes, strictly separated.
    radius, step = Rational{BigInt}(fine.radius), 2*Rational{BigInt}(fine.radius)//16
    @test all(key -> -radius + (key[3]-1)*step > 0, label0)
    @test all(key -> -radius + key[3]*step < 0, label1)
    small = certify_monodromy(SMALL_HOV; slabs=2, dims=8, max_refinements=0)
    @test small.status == :undetermined && small.collision
    @test certify_monodromy(SMALL_HOV; slabs=1, dims=16, max_refinements=0,
                            max_edges=8_000_000).status == :proved
    # Refinement runs only while the vertex budget allows it.
    capped = certify_monodromy(CONSTANT_DN; slabs=2, dims=4, max_refinements=3, max_vertices=600)
    @test capped.status == :undetermined
    @test occursin("max_vertices", capped.reason)
    propagated = certify_monodromy(CONSTANT_DN; slabs=2, dims=2, max_vertices=10)
    @test propagated.status == :failed && isnothing(propagated.partitions)
end

@testset "Closed prism components and initial labels" begin
    grid = GAIO.BoxGrid(GAIO.Box((0.0, 0.0, 0.0, 0.0), (1.0, 1.0, 1.0, 1.0)), (2, 2, 6, 2))
    # Coordinate 3 cells: 1:[-1,-2/3] 2:[-2/3,-1/3] 3:[-1/3,0] 4:[0,1/3] 5:[1/3,2/3] 6:[2/3,1].
    propagated = OnLoops._label_components([[(1, 1, 2, 1), (1, 1, 5, 1)], [(1, 1, 5, 1)]], grid)
    @test !propagated.collision && propagated.components == 2
    @test propagated.partitions[1] == ([(1, 1, 5, 1)], [(1, 1, 2, 1)])
    @test propagated.partitions[2] == ([(1, 1, 5, 1)], NTuple{4,Int}[])
    # One cell straddling Re y = 0 lies in both closed half-planes.
    @test OnLoops._label_components([[(1, 1, 3, 1)]], grid).collision
    # Contacts merge components in one slab, and a bridging chain merges the two
    # labels across time even though neither bridging cell is itself a seed.
    @test OnLoops._label_components([[(1, 1, 2, 1)], [(2, 1, 2, 1)]], grid).components == 1
    @test OnLoops._label_components([[(1, 1, 2, 1), (1, 1, 5, 1)], [(1, 1, 3, 1), (1, 1, 4, 1)]], grid).collision
    # Time 0 is NOT glued to time 1: first and last slabs stay separate components.
    not_glued = OnLoops._label_components([[(1,1,2,1), (1,1,5,1)], [(2,2,6,2)], [(1,1,2,1)]], grid)
    @test not_glued.components == 3 && !not_glued.collision
    @test_throws ArgumentError OnLoops._label_components([NTuple{4,Int}[]], grid)
end

@testset "Devaney-Nitecki gate is exact, not a rational lower bound" begin
    # D = -4c/(|a|+1)^2 - 5 must satisfy D > 0 AND D^2 > 20. A rational lower bound
    # of 2*sqrt(5) on the right-hand side accepts D below 2*sqrt(5) with D^2 < 20.
    below = Rational{BigInt}(44721359545, 10^10)   # 4.4721359545
    above = Rational{BigInt}(4472135955, 10^9)     # 4.472135955
    @test below > Rational{BigInt}(4472135954, 10^9)
    @test below*below < 20
    @test above*above > 20
    for (D, expected) in ((below, false), (above, true))
        c = -(5 + D)
        loop = RationalLoop((0, 1), ((1, 0, c, 0), (1, 0, c, 0)))
        @test _dn_gate(loop.points[1]) == expected
        @test (certify_monodromy(loop).status == :failed) == !expected
        @test (report_monodromy(loop; assume_hyperbolic=true, memory=0, anticipation=0).status == :failed) == !expected
    end
    # The exact boundary D = 2*sqrt(5) is not representable in rationals, so the
    # gate must never accept a rational whose square is at most 20.
    edge = (Rational{BigInt}(1), Rational{BigInt}(0), -(5 + below), Rational{BigInt}(0))
    @test !_dn_gate(edge)
    @test _dn_gate((Rational{BigInt}(1), Rational{BigInt}(0), Rational{BigInt}(-10), Rational{BigInt}(0)))
    @test !_dn_gate((Rational{BigInt}(1), Rational{BigInt}(0), Rational{BigInt}(-3), Rational{BigInt}(0)))
end

@testset "Cylinder dynamic program against full path enumeration" begin
    # Independent reference: enumerate every time-0 vertex that carries a graph
    # path of the right labels over the whole window.
    function reference_cylinder(adjacency, incoming, labels, m, n, word)
        allowed(v, b) = b == 0 ? labels[v][1] : labels[v][2]
        function forward(v, i)
            i == n && return true
            return any(w -> allowed(w, word[m+2+i]) && forward(w, i+1), adjacency[v])
        end
        function backward(v, j)
            j == m && return true
            return any(u -> allowed(u, word[m-j]) && backward(u, j+1), incoming[v])
        end
        return [v for v in 1:length(adjacency)
                if allowed(v, word[m+1]) && forward(v, 0) && backward(v, 0)]
    end
    rng = 20240607
    nextrand() = (rng = (1103515245*rng + 12345) % 2147483648)
    for trial in 1:40
        nvert = 2 + nextrand() % 6
        adjacency = [Int[] for _ in 1:nvert]
        for u in 1:nvert, v in 1:nvert
            nextrand() % 3 == 0 && push!(adjacency[u], v)
        end
        incoming = OnLoops._reverse_graph(adjacency)
        labels = [(nextrand() % 2 == 0, nextrand() % 2 == 0) for _ in 1:nvert]
        for m in 0:2, nn in 0:2
            L = m + nn + 1
            for k in 0:(1 << L)-1
                word = ntuple(i -> (k >> (L - i)) & 1, L)
                expected = reference_cylinder(adjacency, incoming, labels, m, nn, word)
                @test _cylinder_indices(adjacency, incoming, labels, m, nn, word) == expected
            end
        end
    end
    @test_throws DimensionMismatch _cylinder_indices([[Int[]]], [[Int[]]], [(true, true)], 1, 1, (0, 0))
end

@testset "Synthetic shift reports rho = sigma^{-1}, not the inverse action" begin
    # Composed symbolic model: T = sigma, h0 = id, so Q_b = {s : s_{-1} = b} and the
    # reported action is rho = sigma^{-1}, i.e. f(w) = w_{-1}. Vertices are embedded
    # at grid keys 4 apart so that the closed-box contact test is exact separation.
    for (m, n) in ((1, 0), (1, 1), (2, 1), (2, 2))
        L = m + n + 1
        total = 1 << L
        code(u) = ntuple(i -> (u >> (L - i)) & 1, L)
        keys = [(4*(u + 1), 1, 1, 1) for u in 0:total-1]
        adjacency = [Int[] for _ in 1:total]
        for u in 0:total-1, v in 0:total-1
            all(code(v)[j] == code(u)[j+1] for j in 1:L-1) && push!(adjacency[u+1], v+1)
        end
        incoming = OnLoops._reverse_graph(adjacency)
        labels = [(code(u)[m+1] == 0, code(u)[m+1] == 1) for u in 0:total-1]
        q0 = [keys[u+1] for u in 0:total-1 if code(u)[m] == 0]
        q1 = [keys[u+1] for u in 0:total-1 if code(u)[m] == 1]
        @test !isempty(q0) && !isempty(q1)
        for u in 0:total-1
            word = code(u)
            cylinder = _cylinder_indices(adjacency, incoming, labels, m, n, word)
            @test cylinder == [u + 1]
            result = _classify_cylinder(keys[cylinder], q0, q1)
            @test result.output == (word[m] == 0 ? :label0 : :label1)
        end
    end
    # A word whose two ends differ is still read at w_{-1}: for (1,0), w_{-1} = 1
    # while w_{+1} = 0, so the point-action direction would report the wrong bit.
    m, n, L, total = 1, 1, 3, 8
    code3(u) = ntuple(i -> (u >> (L - i)) & 1, L)
    keys = [(4*(u + 1), 1, 1, 1) for u in 0:total-1]
    adjacency = [Int[] for _ in 1:total]
    for u in 0:total-1, v in 0:total-1
        all(code3(v)[j] == code3(u)[j+1] for j in 1:L-1) && push!(adjacency[u+1], v+1)
    end
    incoming = OnLoops._reverse_graph(adjacency)
    labels = [(code3(u)[2] == 0, code3(u)[2] == 1) for u in 0:total-1]
    q0 = [keys[u+1] for u in 0:total-1 if code3(u)[1] == 0]
    q1 = [keys[u+1] for u in 0:total-1 if code3(u)[1] == 1]
    asymmetric = (1, 0, 0)   # w_{-1} = 1, w_0 = 0, w_{+1} = 0
    cylinder = _cylinder_indices(adjacency, incoming, labels, m, n, asymmetric)
    @test _classify_cylinder(keys[cylinder], q0, q1).output == :label1
    @test asymmetric[m] == 1 && asymmetric[m+2] == 0
end

@testset "Cylinder classification truth table" begin
    near = [(1, 1, 1, 1)]
    corner = [(2, 2, 2, 2)]      # touching at a corner
    far = [(9, 1, 1, 1)]
    @test _keys_contact(near, corner) && _keys_contact(near, near)
    @test !_keys_contact(near, far)
    @test _classify_cylinder(near, near, far).output == :label0
    @test _classify_cylinder(near, far, near).output == :label1
    @test _classify_cylinder(near, near, near).output == :undetermined
    @test _classify_cylinder(near, far, far).output == :inconsistent
    @test _classify_cylinder(NTuple{4,Int}[], near, far).output == :inconsistent
    @test _classify_cylinder(near, NTuple{4,Int}[], far).output == :inconsistent
    one = _classify_cylinder(near, corner, far)
    @test one.contact0 && !one.contact1 && one.output == :label0
end

@testset "Candidate monodromy report" begin
    # Hyperbolicity is never verified: the caller must state the assumption.
    bare = report_monodromy(GAMMA_LOOP)
    @test bare.status == :failed && occursin("assume_hyperbolic", bare.reason) && isnothing(bare.table)
    @test report_monodromy(GAMMA_LOOP; assume_hyperbolic=false).status == :failed
    for kwargs in ((; memory=-1), (; anticipation=-1), (; slabs=0), (; max_refinements=-1),
                   (; max_words=0), (; max_vertices=-1), (; max_edges=-1), (; max_words=4))
        result = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, kwargs...)
        @test result.status == :failed
        @test isnothing(result.table)
    end
    # The window size and the lexicographic order are reported, not implied.
    for (m, n) in ((0, 0), (0, 2), (2, 0), (3, 1))
        result = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, memory=m, anticipation=n,
                                  slabs=1, dims=8)
        @test result.window == m + n + 1
        @test length(result.table) == 2^(m + n + 1)
        @test all(length(e.word) == m + n + 1 for e in result.table)
        @test [e.word for e in result.table] == sort([e.word for e in result.table])
        @test result.status != :proved
    end
    # Constant DN loop: the action is the identity, f(w) = w_0, once the grid separates.
    fine = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, memory=1, anticipation=1,
                            slabs=1, dims=16, max_edges=8_000_000)
    @test fine.status == :candidate
    @test fine.collision == false
    @test count(e -> e.output == :label0, fine.table) == 4
    @test all(e -> e.output == (e.word[2] == 0 ? :label0 : :label1), fine.table)
    @test fine.endpoint.label0 > 0 && fine.endpoint.label1 > 0
    @test fine.base.core > 0 && fine.base.vertices > fine.base.core
    @test fine.seedless.components == 0
    @test fine.refinements == 0
    md = monodromy_markdown(fine)
    @test occursin("rho = h1", md) && occursin("output 0", md) && occursin("monodromy", md)
    @test count(line -> startswith(line, "| "), split(md, '\n')) == length(fine.table) + 2
    # A coarse enclosure may leave words unresolved, but must not determine a wrong bit.
    coarse = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, memory=1, anticipation=1,
                              slabs=1, dims=8)
    @test coarse.status == :undetermined
    @test coarse.table !== nothing
    @test all(e -> (e.output != :label0 || e.word[2] == 0) &&
                   (e.output != :label1 || e.word[2] == 1), coarse.table)
    @test monodromy_markdown(coarse) != ""
    # Finite refinement recomputes enclosures on the finer grid and stops in budget.
    refined = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, memory=1, anticipation=1,
                               slabs=1, dims=8, max_refinements=1, max_edges=8_000_000)
    @test refined.status == :candidate && refined.refinements == 1 && refined.dims == (16, 16, 16, 16)
    capped = report_monodromy(CONSTANT_DN; assume_hyperbolic=true, memory=1, anticipation=1,
                              slabs=1, dims=8, max_refinements=1, max_vertices=60_000)
    @test capped.status == :undetermined && occursin("max_vertices", capped.reason)
    # The paper's gamma loop stays a candidate report; it is never a proof path.
    small = report_monodromy(GAMMA_LOOP; assume_hyperbolic=true, memory=0, anticipation=0,
                             slabs=2, dims=4, max_edges=2_000_000)
    @test small.status in (:candidate, :undetermined, :failed)
    @test occursin("NOT verified", small.claim)
    @test isnothing(report_monodromy(GAMMA_LOOP; assume_hyperbolic=true, memory=0,
                                     anticipation=0, slabs=0).table)
end

@testset "Monodromy revalidates mutable paths and preflights allocations" begin
    for corrupt in (
        loop -> (loop.points[end] = (1//1,0//1,-9//1,0//1)),
        loop -> (loop.times[end] = 2//1),
        loop -> push!(loop.times,2//1),
        loop -> empty!(loop.points))
        loop = RationalLoop((0,1),((1,0,-10,0),(1,0,-10,0)))
        corrupt(loop)
        @test_throws ArgumentError OnLoops._loop_geometry_check(loop)
        @test certify_monodromy(loop; dims=2, max_refinements=0).status == :failed
        @test report_monodromy(loop; assume_hyperbolic=true, dims=2).status == :failed
    end
    # Both budgets are deliberately tiny; no enormous vector may be allocated.
    for certify in (certify_monodromy,
                    (loop; kwargs...) -> report_monodromy(loop; assume_hyperbolic=true, kwargs...))
        r = certify(CONSTANT_DN; slabs=typemax(Int),dims=2,max_vertices=256)
        @test r.status == :failed && occursin("max_vertices",r.reason)
    end
    huge = report_monodromy(CONSTANT_DN; assume_hyperbolic=true,
                           memory=typemax(Int), anticipation=typemax(Int))
    @test huge.status == :failed && occursin("symbolic window",huge.reason)
end

