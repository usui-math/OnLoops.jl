@testset "Exact Hermitian rectangle verification" begin
    R = Rational{BigInt}
    z = R(0)
    Q = (R(1), z, z, R(-1//4))
    box = (R(13//20), R(3//4), R(-1//20), R(1//20))
    b = OnLoops._cone_hermitian_bounds(Q, Q, R(1//4), box)
    @test b.determinant_min > 0
    @test OnLoops._cone_hermitian_margin(Q, Q, R(1//4), box) > 0
    eq = (R(5//8), R(5//8), z, z)
    @test OnLoops._cone_hermitian_margin(Q, Q, R(1//4), eq) == 0
    @test OnLoops._cone_hermitian_margin(Q, Q, R(1//4), (z,z,z,z)) < 0
    @test OnLoops._cone_radial_extrema(R(2),R(-4),R(8),R(5),
                                       (R(0),R(2),R(-3),R(0))) == (R(-5),R(5))
    @test OnLoops._cone_radial_extrema(R(-1),z,z,z,
                                       (R(-2),R(1),R(-3),R(1))) == (R(-13),z)
    matrix(q) = Complex{R}[q[1] complex(q[2],q[3]); complex(q[2],-q[3]) q[4]]
    for t in 1:40
        src = (R(t%5-2),R(t%7-3,8),R(t%3-1,4),R(t%11-5,8))
        dst = (R(t%7-2,4),R(t%5-1,8),R(t%11-5,8),R(t%3-2))
        a = R(t%5+1,8)
        rect = (R(-3//4),R(1//2),R(-1//3),R(2//3))
        bounds = OnLoops._cone_hermitian_bounds(src,dst,a,rect)
        margin = OnLoops._cone_hermitian_margin(src,dst,a,rect)
        for u in (rect[1],(rect[1]+rect[2])/2,rect[2]),
            v in (rect[3],(rect[3]+rect[4])/2,rect[4])
            M = Complex{R}[2complex(u,v) -a; 1 0]
            A = M'*matrix(dst)*M-matrix(src)
            det = real(A[1,1])*real(A[2,2])-abs2(A[1,2])
            polynomial = bounds.coefficients
            expected = polynomial[1]*(u^2+v^2)+polynomial[2]*u+polynomial[3]*v+polynomial[4]
            @test expected == det
            @test bounds.determinant_min <= det
            @test bounds.a11_min <= real(A[1,1]) <= bounds.a11_max
            if margin > 0
                @test real(A[1,1])-margin >= 0
                @test real(A[2,2])-margin >= 0
                @test (real(A[1,1])-margin)*(real(A[2,2])-margin)-abs2(A[1,2]) >= 0
            end
        end
    end
end

@testset "Complex cone proof covers nonreal base states" begin
    p = map(input_interval,(1//4,0,-10,0))
    proved = certify_cone_field(p; dims=(12,8), iterations=1)
    @test proved.scope == :complex_state
    @test proved.status == :proved
    @test proved.margin > 0
    @test proved.state_dims == (12,12,8,8)
    @test proved.edges >= proved.constraints > 0
    @test proved.forms !== nothing
    repeat = certify_cone_field(p; dims=(12,8), iterations=1)
    @test repeat.margin == proved.margin && repeat.forms == proved.forms
    for (a,c) in ((1,0),(1//4,25//64),(1//4,-75//64))
        r = certify_cone_field(map(input_interval,(a,0,c,0)); dims=(4,4), iterations=5)
        @test r.status != :proved
        @test r.scope == :complex_state
    end
    box = (input_interval(1//4),input_interval(0),interval(Float64,-10,-9),interval(Float64,0,1//2))
    r = certify_cone_field(box; dims=(8,4), iterations=10)
    @test r.scope == :complex_state && r.core > 0
    for kw in ((;dims=(0,2)),(;samples=0),(;iterations=0),(;samples=big(typemax(Int))+1),
               (;dims=(big(typemax(Int))+1,2)),(;max_edges=0),(;max_vertices=0),(;radius=1))
        @test certify_cone_field(p;kw...).status == :failed
    end
    unsupported = (interval(Float64,1//4,1//2),input_interval(0),input_interval(-10),input_interval(0))
    @test certify_cone_field(unsupported;dims=(4,4)).status == :undetermined
end

@testset "Cone search hint is a hint, not a certificate" begin
    p = map(input_interval,(1//4,0,-10,0))
    base = certify_cone_field(p; dims=(12,8), iterations=1)
    @test base.status == :proved
    # The internal default hint is (1,0,0,-|a|); passing it explicitly must
    # reproduce the default search exactly.
    same = certify_cone_field(p; dims=(12,8), iterations=1,
                              initial_forms=box -> (1.0,0.0,0.0,-0.25))
    @test same.status == :proved && same.margin == base.margin && same.forms == base.forms
    # A different finite hint changes the explored family but never the verdict rule.
    other = certify_cone_field(p; dims=(12,8), iterations=1,
                               initial_forms=box -> (0.0,0.5,0.0,0.0))
    @test other.scope == :complex_state
    @test other.status != :proved || other.margin > 0
    # A hint that cannot be used is a failure, never a silent acceptance.
    for bad in (1, [1.0,0.0,0.0,-0.25], box -> (Inf,0.0,0.0,1.0), box -> (1.0,0.0))
        @test certify_cone_field(p; dims=(4,4), iterations=1, initial_forms=bad).status == :failed
    end
end
