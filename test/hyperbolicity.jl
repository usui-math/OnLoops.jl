import OnLoops
using OnLoops: henon_radius, fiber_isolated, certify_hyperbolicity, certify_cone_field,
               certify_real_cone_field

parameter_box(a, ai, c, ci) = map(input_interval, (a, ai, c, ci))

@testset "Uniform complex Hénon radius" begin
    @test henon_radius(parameter_box(1, 0, 0, 0)) == 2.0
    p = parameter_box(1, 0, -10, 0)
    r = henon_radius(p)
    q = Rational{BigInt}(r)
    @test 4.3 < r < 4.4
    @test q >= 2 && q^2 - 2*q - 10 >= 0
    data = OnLoops._henon_data(p)
    @test (data.a_upper, data.c_upper, data.c_lower) == (1, 10, 10)
    crossing = (interval(-1, 1), interval(Float64, 1//2, 1), interval(-3, 2), interval(4, 5))
    data = OnLoops._henon_data(crossing)
    @test data.a_upper^2 >= 2
    @test data.c_upper^2 >= 34
    @test data.c_lower == 4  # real c crosses zero; do not use endpoint-square minima
    r = Rational{BigInt}(henon_radius(crossing))
    @test r^2 - (1+data.a_upper)*r - data.c_upper >= 0
    @test_throws ArgumentError henon_radius(parameter_box(0, 0, -10, 0))
    @test_throws ArgumentError henon_radius((interval(-1, 1), interval(-1, 1), interval(-100), interval(0)))
    @test_throws ArgumentError henon_radius((interval(1), nai(), interval(-10), interval(0)))
end

@testset "Strict relative fiber isolation" begin
    for (n, expected) in ((4, false), (8, true))
        # Known invariant base point 0 is on the LEFT BASE FACE, not ambient interior.
        G = GAIO.BoxGrid(GAIO.Box((0.5, 0.0), (0.5, 1.0)), (1, n))
        g = outer_graph(zv -> (interval(0), zv[2]+zv[2]), GAIO.cover(G, :))
        W = GAIO.BoxSet(G, Set(g.keys[graph_core(g.adjacency)]))
        @test fiber_isolated(W; base_dimension=1) == expected
        @test !isempty(W)
        if n == 8
            @test W.set == Set([(1, 3), (1, 4), (1, 5), (1, 6)])
        end
    end
    G = GAIO.BoxGrid(GAIO.Box((0.5, 0.0), (0.5, 1.0)), (1, 8))
    @test fiber_isolated(GAIO.BoxSet(G, Set([(1, 7)])); base_dimension=1)
    @test !fiber_isolated(GAIO.BoxSet(G, Set([(1, 8)])); base_dimension=1)
    @test !fiber_isolated(GAIO.BoxSet(G); base_dimension=1)
    @test_throws ArgumentError fiber_isolated(GAIO.BoxSet(G); base_dimension=0)
    @test_throws ArgumentError fiber_isolated(GAIO.BoxSet(G); base_dimension=2)
    @test_throws BoundsError fiber_isolated(GAIO.BoxSet(G, Set([(1, 9)])); base_dimension=1)
    basegrid = GAIO.BoxGrid(GAIO.Box((1.0, 1.0, 0.0, 0.0), (1.0, 1.0, 1.0, 1.0)), (4, 4, 1, 1))
    @test OnLoops._base_x_minimum(GAIO.BoxSet(basegrid, Set([(3, 3, 1, 1)]))) == 2
    @test OnLoops._base_x_minimum(GAIO.BoxSet(basegrid, Set([(1, 1, 1, 1)]))) == 0
    @test_throws ArgumentError OnLoops._base_x_minimum(GAIO.BoxSet(basegrid))
end

@testset "Actual Hénon positive certificate and parameter box" begin
    p = parameter_box(1, 0, -10, 0)
    result = certify_hyperbolicity(p)
    @test result.status == :proved
    @test result.method == :global_dominance
    @test isnothing(result.base) && isnothing(result.tangent)
    @test result.radius == henon_radius(p)
    @test all(isguaranteed, result.parameters)
    # Entire four-dimensional parameter rectangle, not just its center.
    e = 1//1024
    P = (interval(Float64, 1-e, 1+e), interval(Float64, -e, e),
         interval(Float64, -10-e, -10+e), interval(Float64, -e, e))
    result = certify_hyperbolicity(P)
    @test result.status == :proved && result.method == :global_dominance
    result = certify_hyperbolicity(p; radius=13//3)
    @test result.status == :proved
    @test Rational{BigInt}(result.radius) >= 13//3
    @test certify_hyperbolicity(p; radius=4).status == :failed  # analytic shortcut MUST NOT bypass coverage
    @test certify_hyperbolicity(p; max_vertices=0, max_edges=0).status == :proved
    # Crossing Re(a)=0 is eligible when Im(a) excludes zero uniformly.
    P = (interval(-1, 1), interval(Float64, 1//2, 1), interval(-100), interval(0))
    @test certify_hyperbolicity(P).status == :proved
end

@testset "Compare complete historical parameter cubes" begin
    # The first cube of Arai's a = 1/4 table (supplemental materials) specifies this ENTIRE box, plus its complex conjugate.
    # Reprove via exact modulus inequalities, not the table's row counts or centers.
    for imaginary in (interval(Float64, 0, 1//2), interval(Float64, -1//2, 0))
        p = (input_interval(1//4), input_interval(0), interval(Float64, -8, -31//4), imaginary)
        result = certify_hyperbolicity(p)
        @test result.status == :proved
        @test all(isequal_interval(result.parameters[k], p[k]) for k in 1:4)
    end
    # The first cube of Arai's a = 1 table: the old claim does NOT turn a coarse unresolved attempt into proof.
    p = (input_interval(1), input_interval(0), interval(Float64, -8, -31//4), interval(Float64, 0, 1//4))
    @test certify_hyperbolicity(p; base_dims=(1,1,1,1), fiber_dims=(2,2,2,2)).status == :undetermined
end

@testset "Bounded nonzero tangent orbits cannot certify" begin
    one = (1, 1, 1, 1)
    two = (2, 2, 2, 2)
    result = certify_hyperbolicity(parameter_box(1, 0, 0, 0); base_dims=one, fiber_dims=two)
    @test result.status == :undetermined
    @test result.method == :tangent_graph
    @test !isempty(result.base) && !isempty(result.tangent)
    @test !fiber_isolated(result.tangent; base_dimension=4)
    # DH at the origin has a REAL nonzero four-cycle (v,w) -> (-w,v).
    for (v, w) in ((1, 0), (0, 1), (-1, 0), (0, -1))
        point = (0, 0, 0, 0, v, 0, w, 0)
        @test any(all(contains_exact(closed_box(result.tangent.partition, key)[k], point[k]) for k in 1:8)
                  for key in result.tangent.set)
    end
    # Equality 2|x|=1+|a| at fixed (x,y)=(1,1) must NOT pass a strict shortcut.
    p = parameter_box(1, 0, 1, 0)
    @test henon_tangent((1, 0, 1, 0), (1, 0, 1, 0), (1, 0, 1, 0)) == (1, 0, 1, 0)
    @test certify_hyperbolicity(p; base_dims=one, fiber_dims=two).status == :undetermined
end

@testset "Tangent graph completes over the base kernel but stays unisolated" begin
    # This budgeted example must stay a non-proof; equal graph candidates and
    # boundary contact here do not establish failure at every resolution.
    p = parameter_box(1//4, 0, -3//2, 0)
    r = henon_radius(p)
    bdims, fdims = (4, 4, 4, 4), (2, 2, 2, 2)
    G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> r, 4)), bdims)
    bg = outer_graph(z -> OnLoops.henon(z, OnLoops._henon_data(p).parameters), GAIO.cover(G, :);
                     max_edges=1_000_000)
    recurrent = Set(bg.keys[recurrent_vertices(bg.adjacency)])
    kernel = Set(bg.keys[graph_core(bg.adjacency)])
    @test recurrent == kernel  # the prune gain is 1.0: nothing is dropped
    TG = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 8),
                              (ntuple(_ -> r, 4)..., 1.0, 1.0, 1.0, 1.0)), (bdims..., fdims...))
    initial = Set{NTuple{8,Int}}()
    for key in kernel, fiber in CartesianIndices(fdims)
        push!(initial, (key..., Tuple(fiber)...))
    end
    tg = outer_graph(zv -> tangent_lift(zv, OnLoops._henon_data(p).parameters),
                     GAIO.BoxSet(TG, initial); max_edges=3_000_000)
    tangent = GAIO.BoxSet(TG, Set(tg.keys[graph_core(tg.adjacency)]))
    @test !isempty(tangent.set)
    # The kernel reaches the far fiber boundary: the strict interior test fails.
    @test !fiber_isolated(tangent; base_dimension=4)
    @test any(key[8] == fdims[4] for key in tangent.set)
end

@testset "Fixed points expose real-state and unit-eigenvalue scope" begin
    a = 1//4
    # One unit eigenvalue already supplies a nonzero two-sided bounded vector.
    for (x, c, mu) in ((5//8, 25//64, 1), (-5//8, -75//64, -1))
        z = (x, 0//1, x, 0//1)
        p = (a, 0//1, c, 0//1)
        v = (1//1, 0//1, mu//1, 0//1)
        @test henon(z, p) == z
        @test henon_tangent(z, v, p) == mu .* v
        @test abs(a/mu) < 1
    end
    # A nonreal fixed point exists for exact real parameters.
    z = (5//8, 5//8, 5//8, 5//8)
    @test henon(z, (a, 0//1, 25//32, 0//1)) == z
    @test z[2] != 0 && z[4] != 0
    # Negating every unrestricted form reverses the inequality direction.
    R = Rational{BigInt}
    Q = R[1 0; 0 -a]
    M = R[4 -a; 1 0]
    A = M' * Q * M - Q
    @test A[1,1] > 0 && A[2,2] > 0 && A[1,1]*A[2,2] - A[1,2]^2 > 0
    @test (-Q) - M' * (-Q) * M == A
    # Work in Q(sqrt(34)); no numerical crossing is used as evidence of equality.
    mul(s,t) = (s[1]*t[1]+34s[2]*t[2],s[1]*t[2]+s[2]*t[1])
    x,y = (R(-5//8),R(1//8)),(R(-5//8),R(-1//8))
    c = R(-109//64)
    hx = mul(x,x) .+ (c,R(0)) .- a .* y
    hy = mul(y,y) .+ (c,R(0)) .- a .* x
    @test hx == y && hy == x
    @test x != y
    xy = mul(x,y)
    @test xy == ((1+a)^2+c,R(0))
    trace = 4xy[1]-2a
    determinant = a^2
    @test determinant+trace+1 == 0 # period-two derivative has multiplier -1
    @test determinant < 1
end

@testset "Failure is not proof or nonhyperbolicity" begin
    positive = parameter_box(1, 0, -10, 0)
    negative = parameter_box(1, 0, 0, 0)
    for p in ((1.0, 0.0, -10.0, 0.0), (interval(1), interval(0), interval(-10)),
              parameter_box(0, 0, -100, 0),
              (interval(1), emptyinterval(), interval(-10), interval(0)),
              (interval(1), nai(), interval(-10), interval(0)),
              (interval(1), entireinterval(), interval(-10), interval(0)),
              (convert(Interval{Float64}, 1), interval(0), interval(-10), interval(0)))
        @test certify_hyperbolicity(p).status == :failed
    end
    for kwargs in ((; base_dims=(0, 1, 1, 1)), (; base_dims=(1, 1, 1)),
                   (; fiber_dims=(1.0, 1, 1, 1)), (; fiber_dims=(big(typemax(Int))+1, 1, 1, 1)),
                   (; max_vertices=-1), (; max_edges=-1), (; max_edges=0.5),
                   (; radius=-1), (; radius=Inf), (; radius=interval(4, 5)))
        @test certify_hyperbolicity(positive; kwargs...).status == :failed
    end
    result = certify_hyperbolicity(negative; base_dims=(1, 1, 1, 1), fiber_dims=(2, 2, 2, 2), max_vertices=1)
    @test result.status == :failed && !isnothing(result.base) && isnothing(result.tangent)
    @test certify_hyperbolicity(negative; max_vertices=0).status == :failed
    @test certify_hyperbolicity(negative; base_dims=(1, 1, 1, 1), max_edges=0).status == :failed
    @test certify_hyperbolicity(negative; base_dims=(typemax(Int), typemax(Int), 1, 1)).status == :failed
end

@testset "Cellwise strict cone condition on real parameter slices" begin
    a = 1//4
    # The uniform form Q = diag(1,-a) satisfies the INCREASING direction exactly on
    # |x| > (1+a)/2, so the rigorous margin decides the threshold cell by cell.
    to_big(x) = Rational{BigInt}(x)
    Q = Rational{BigInt}[1 0; 0 -a]
    margin(alo, ahi, xl, xh) = OnLoops._cone_edge_margin(Q, Q, to_big(alo), to_big(ahi),
                                                       to_big(xl), to_big(xh))
    @test margin(a, a, 13//20, 3//4) > 0
    @test margin(a, a, 5//8, 5//8) == 0                # equality is not strict
    @test margin(a, a, -1//10, 1//10) < 0              # contains x = 0
    @test margin(a, a, -3//4, -13//20) > 0             # |x| above the threshold
    @test margin(a, a, -3//5, -11//20) < 0             # |x| below it
    # A wider parameter interval cannot have a larger margin at the same cell.
    @test margin(1//4, 1//2, 13//20, 3//4) <= margin(5//16, 5//16, 13//20, 3//4)
    # Cellwise forms certify cells far below the uniform threshold.
    p3 = parameter_box(1//4, 0, -3//1, 0)
    proved = certify_real_cone_field(p3; dims=(32, 32), iterations=1200, max_edges=20_000_000)
    @test proved.status == :proved
    @test proved.margin > 0
    @test proved.edges > 0 && proved.core > 0 && proved.cells == proved.core
    @test occursin("cellwise strict cone condition", proved.reason)
    @test occursin("width", proved.reason)
    for c in (-13//4, -7//2)
        @test certify_real_cone_field(parameter_box(1//4, 0, c, 0); dims=(32, 32), iterations=1200,
                                 max_edges=20_000_000).status == :proved
    end
    # Below the feasible band the family is NOT found: report undetermined, never proved.
    for c in (-5//2, -11//4)
        below = certify_real_cone_field(parameter_box(1//4, 0, c, 0); dims=(32, 32), iterations=1200,
                                   max_edges=20_000_000)
        @test below.status == :undetermined
        @test below.margin <= 0
    end
    # Bounded nonzero tangent orbits must never be certified: the origin four-cycle
    # of H_{1,0} and the equality case H_{1,1}.
    for (a1, c1) in ((1//1, 0//1), (1//1, 1//1))
        control = certify_real_cone_field(parameter_box(a1, 0, c1, 0); dims=(24, 24), iterations=800)
        @test control.status == :undetermined
        @test control.margin <= 0
    end
    # Complex boxes are out of scope and are never silently proved or failed.
    complex_box = (input_interval(1//4), input_interval(0),
                   interval(Float64, -3), interval(Float64, 0, 1//2))
    skipped = certify_real_cone_field(complex_box)
    @test skipped.status == :undetermined
    @test occursin("real parameters", skipped.reason)
    @test skipped.edges == 0
    # Real-state success must not reach the global complex certificate.
    integrated = certify_hyperbolicity(p3; base_dims=(1, 1, 1, 1), fiber_dims=(1, 1, 1, 1),
                                       cone_dims=(2,2), cone_iterations=1)
    @test integrated.status != :proved
    @test integrated.cone.scope == :complex_state
    @test proved.scope == :real_state
    analytic = certify_hyperbolicity(parameter_box(1, 0, -10, 0))
    @test analytic.method == :global_dominance && isnothing(analytic.cone)
    # Budgets and invalid settings fail instead of returning a partial proof.
    for kwargs in ((; dims=(32,)), (; dims=(0, 32)), (; dims=(32, 1.0)),
                   (; iterations=0), (; samples=-1), (; max_vertices=-1), (; max_edges=-1))
        @test certify_real_cone_field(p3; kwargs...).status == :failed
    end
    @test certify_real_cone_field(p3; dims=(32, 32), max_edges=10).status == :failed
    @test certify_real_cone_field(p3; dims=(4, 4), max_vertices=4).status == :failed
    @test certify_real_cone_field(parameter_box(0, 0, -3, 0); dims=(8, 8)).status == :failed
    @test certify_real_cone_field(p3; dims=(64, 64), max_edges=0).status == :failed
end
