using Test
using OnLoops: henon, henon_tangent, tangent_lift, input_interval, beta, gamma
using IntervalArithmetic: Interval, interval, inf, sup, isguaranteed, isequal_interval,
                          emptyinterval, nai, entireinterval
using KernelAbstractions
import GAIO

# Ordinary floating-point plumbing only: this kernel is NOT a rigorous box image.
@kernel function point_images!(output, input, p)
    i = @index(Global, Linear)
    output[i] = henon(input[i], p)
end

@testset "Hénon coordinate convention" begin
    p = (0.25, -0.5, -2.0, 0.75)
    z = (1.0, 0.5, -0.25, 0.75)
    x, y = complex(z[1], z[2]), complex(z[3], z[4])
    a, c = complex(p[1], p[2]), complex(p[3], p[4])
    X = x^2 + c - a*y
    @test henon(z, p) == (real(X), imag(X), real(x), imag(x))
end

@testset "CPU interval enclosure" begin
    zero_interval = interval(0.0)
    z = (interval(-1.0, 1.0), zero_interval, interval(-2.0, 3.0), interval(-3.0, 2.0))
    p = (zero_interval, zero_interval, interval(-1.0), zero_interval)
    image = henon(z, p)
    @test inf(image[1]) == -1.0
    @test sup(image[1]) == 0.0
    @test (inf(image[3]), sup(image[3])) == (-1.0, 1.0)

    # Exact rational reference, including interiors and nonzero imaginary parameters.
    bounds = ((-1//1, 1//1), (-1//2, 1//2), (-2//1, 1//1), (-1//1, 2//1))
    parameter_bounds = ((1//4, 1//2), (-1//2, 1//4), (-2//1, -1//1), (0//1, 3//4))
    state_box = map(b -> interval(Float64(b[1]), Float64(b[2])), bounds)
    parameter_box = map(b -> interval(Float64(b[1]), Float64(b[2])), parameter_bounds)
    enclosure = henon(state_box, parameter_box)
    samples = map(b -> (b[1], (b[1]+b[2])/2, b[2]), (bounds..., parameter_bounds...))
    for s in Iterators.product(samples...)
        x, y = complex(s[1], s[2]), complex(s[3], s[4])
        a, c = complex(s[5], s[6]), complex(s[7], s[8])
        X = x^2 + c - a*y
        exact = (real(X), imag(X), real(x), imag(x))
        @test all(Rational{BigInt}(inf(enclosure[k])) <= exact[k] <= Rational{BigInt}(sup(enclosure[k])) for k in 1:4)
    end
end

# Compare endpoints as exact rationals: never round the oracle to Float64.
contains_exact(I, q) = Rational{BigInt}(inf(I)) <= q <= Rational{BigInt}(sup(I))

@testset "Exact input construction" begin
    for (text, q) in (("0.1", 1//10), ("-0.1", -1//10), ("1e-20", big(1)//big(10)^20),
                      ("1/3", 1//3), ("9007199254740993", big(9007199254740993)//1))
        I = input_interval(text)
        @test contains_exact(I, q)
        @test isguaranteed(I)
        @test contains_exact(input_interval(q), q)
    end
    @test contains_exact(input_interval(9007199254740993), big(9007199254740993)//1)
    @test !contains_exact(interval(0.1), 1//10)  # nearest Float64 is not decimal input
    @test_throws MethodError input_interval(0.1)
    for text in ("[0.1,0.2]", "0.1?1", "0.1_com", "[empty]", "[nai]", "garbage",
                 "Inf", "NaN", "1e400", "1/0")
        @test_throws ArgumentError input_interval(text)
    end
    @test_throws ArgumentError input_interval(big(10)^400)
end

@testset "Tangent and lifted Hénon map" begin
    z = (1//3, -1//5, 2//7, -3//8)
    p = (1//4, -1//2, -2//1, 3//4)
    v = (-2//3, 1//7, 3//5, -2//9)
    x, a = complex(z[1], z[2]), complex(p[1], p[2])
    V = 2*x*complex(v[1], v[2]) - a*complex(v[3], v[4])
    @test henon_tangent(z, v, p) == (real(V), imag(V), v[1], v[2])
    @test tangent_lift((z..., v...), p) == (henon(z, p)..., henon_tangent(z, v, p)...)

    bounds = ((-1//1, 1//1), (-1//2, 1//2), (1//4, 1//2), (-1//2, 1//4),
              (-2//1, 1//1), (-1//1, 2//1), (-3//4, 1//2), (-1//2, 3//4))
    I = map(b -> interval(Float64, b...), bounds)
    state = (I[1], I[2], interval(-2, 3), interval(-3, 2))
    parameter = (I[3], I[4], input_interval("-2.1"), input_interval("0.1"))
    direction = (I[5], I[6], I[7], I[8])
    image = henon_tangent(state, direction, parameter)
    lift = tangent_lift((state..., direction...), parameter)
    @test all(isguaranteed, image)
    @test all(isguaranteed, lift)
    @test all(isequal_interval(lift[k], henon(state, parameter)[k]) for k in 1:4)
    @test all(isequal_interval(lift[k+4], image[k]) for k in 1:4)
    @test isequal_interval(image[3], direction[1])
    @test isequal_interval(image[4], direction[2])
    samples = map(b -> (b[1], (b[1]+b[2])/2, b[2]), bounds)
    for s in Iterators.product(samples...)
        x, a = complex(s[1], s[2]), complex(s[3], s[4])
        v, w = complex(s[5], s[6]), complex(s[7], s[8])
        V = 2*x*v - a*w
        @test all(contains_exact(image[k], q) for (k, q) in enumerate((real(V), imag(V), real(v), imag(v))))
    end
end

# Independent scalar rational formulas, not calls to the implementation's knots.
function exact_beta(t)
    cr, ci = if t <= 1//8
        (-11//4, -2*t)
    elseif t <= 3//8
        (-11//4 + 2*(t-1//8), -1//4)
    elseif t <= 5//8
        (-9//4, -1//4 + 2*(t-3//8))
    elseif t <= 7//8
        (-9//4 - 2*(t-5//8), 1//4)
    else
        (-11//4, 1//4 - 2*(t-7//8))
    end
    return (1//4, 0//1, cr, ci)
end

function exact_gamma(t)
    if t <= 1//16
        return (1 - 12*t, 0//1, -10//1, 0//1)
    elseif t <= 7//16
        return (1//4, 0//1, -10 + (58//3)*(t-1//16), 0//1)
    elseif t <= 9//16
        return exact_beta(8*(t-7//16))
    elseif t <= 15//16
        return (1//4, 0//1, -11//4 - (58//3)*(t-9//16), 0//1)
    else
        return (1//4 + 12*(t-15//16), 0//1, -10//1, 0//1)
    end
end

@testset "Whole-time loop enclosures" begin
    beta_knots = (0//1, 1//8, 3//8, 5//8, 7//8, 1//1)
    gamma_knots = (0//1, 1//16, 7//16, 29//64, 31//64, 33//64, 35//64, 9//16, 15//16, 1//1)
    for (loop, oracle, knots) in ((beta, exact_beta, beta_knots), (gamma, exact_gamma, gamma_knots))
        # Includes degenerate time intervals, all fold crossings, and both endpoints.
        for lo in 0:64, hi in lo:64
            qlo, qhi = lo//64, hi//64
            image = loop(interval(Float64, qlo, qhi))
            critical_times = [qlo, qhi, (qlo+qhi)/2, filter(t -> qlo <= t <= qhi, knots)...]
            values = oracle.(critical_times)
            @test all(contains_exact(image[k], minimum(v[k] for v in values)) &&
                      contains_exact(image[k], maximum(v[k] for v in values)) for k in 1:4)
            @test all(isguaranteed, image)
        end
        @test all(isequal_interval(loop(interval(0))[k], loop(interval(1))[k]) for k in 1:4)
        for bad in (emptyinterval(), nai(), entireinterval(), interval(Float64, -1//64, 0),
                    interval(Float64, 1, 65//64), convert(Interval{Float64}, 0.5))
            @test_throws ArgumentError loop(bad)
        end
        @test_throws MethodError loop(0.5)
        @test all(contains_exact(loop(input_interval("0.1"))[k], oracle(1//10)[k]) for k in 1:4)
        for T in (Float32, BigFloat)
            image = loop(interval(T, 1//10, 9//10))
            @test all(contains_exact(image[k], oracle(t)[k]) for k in 1:4 for t in knots if 1//10 <= t <= 9//10)
            @test all(isguaranteed, image)
        end
    end
    b = beta(interval(Float64, 1//8 - 1//1024, 1//8 + 1//1024))
    @test inf(b[3]) == -2.75 && sup(b[3]) == -2.75 + 1/512
    @test inf(b[4]) == -0.25 && sup(b[4]) == -0.25 + 1/512
    # Gamma's embedded beta folds must not escape their local two segments.
    g = gamma(interval(Float64, 29//64 - 1//1024, 29//64 + 1//1024))
    @test inf(g[3]) == -2.75 && sup(g[3]) == -2.75 + 1/64
    @test inf(g[4]) == -0.25 && sup(g[4]) == -0.25 + 1/64
    @test (inf(gamma(interval(0, 1))[3]), sup(gamma(interval(0, 1))[3])) == (-10.0, -2.25)
end

@testset "GAIO box infrastructure (not certification)" begin
    domain = GAIO.Box((0.0, 0.0, 0.0, 0.0), (2.0, 2.0, 2.0, 2.0))
    grid = GAIO.BoxGrid(domain, (2, 2, 2, 2))
    boxes = GAIO.cover(grid, :)
    @test length(boxes) == 16
end

@testset "KernelAbstractions CPU point evaluation" begin
    # Non-workgroup-multiple size also exercises automatic bounds handling.
    input = [(i/16, -i/32, i/64, -i/128) for i in 1:67]
    output = similar(input)
    p = (0.25, 0.0, -2.0, 0.25)
    backend = CPU()
    point_images!(backend, 32)(output, input, p; ndrange=length(input))
    KernelAbstractions.synchronize(backend)
    @test output == henon.(input, Ref(p))
end

include("sets_graphs.jl")
include("hyperbolicity.jl")
include("cone_complex.jl")
include("monodromy.jl")
