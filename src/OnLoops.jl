module OnLoops

using IntervalArithmetic: Interval, interval, inf, sup, isnai, isempty_interval,
                          isguaranteed, intersect_interval, hull

export henon, henon_tangent, tangent_lift, input_interval, beta, gamma,
       RationalLoop, loop_box, BETA_LOOP, GAMMA_LOOP

"""
    henon(z::NTuple{4}, p::NTuple{4})

Real coordinates of `(x² + c - a*y, x)`.
State order: `(real(x), imag(x), real(y), imag(y))`.
Parameter order: `(real(a), imag(a), real(c), imag(c))`.
Use real CPU intervals for box enclosures; floating-point inputs give point
approximations only. This function does not certify hyperbolicity.
"""
@inline function henon(z::NTuple{4}, p::NTuple{4})
    xr, xi, yr, yi = z
    ar, ai, cr, ci = p
    return (xr^2 - xi^2 + cr - ar*yr + ai*yi,
            (xr+xr)*xi + ci - ar*yi - ai*yr,
            xr, xi)
end

"""
    henon_tangent(z::NTuple{4}, v::NTuple{4}, p::NTuple{4})

Real coordinates of `DH(z)(v,w) = (2x*v - a*w, v)`. Direction order is
`(real(v), imag(v), real(w), imag(w))`. Arithmetic kernel only; like `henon`,
this does not validate inputs or certify hyperbolicity.
"""
@inline function henon_tangent(z::NTuple{4}, v::NTuple{4}, p::NTuple{4})
    xr, xi = z[1], z[2]
    ar, ai = p[1], p[2]
    vr, vi, wr, wi = v
    # Doubling by addition avoids implicit Real -> Interval conversions, which
    # discard IntervalArithmetic's guarantee flag even for the integer 2.
    return ((xr+xr)*vr - (xi+xi)*vi - ar*wr + ai*wi,
            (xr+xr)*vi + (xi+xi)*vr - ar*wi - ai*wr,
            vr, vi)
end

"""
    tangent_lift(zv::NTuple{8}, p::NTuple{4})

Map state and tangent direction together. The first four coordinates are the
state, the last four the direction. Carry entire intervals, never midpoints.
"""
@inline function tangent_lift(zv::NTuple{8}, p::NTuple{4})
    z, v = zv[1:4], zv[5:8]
    return (henon(z, p)..., henon_tangent(z, v, p)...)
end

function _checked_interval(x::Interval)
    (!isnai(x) && !isempty_interval(x) && isguaranteed(x) &&
     isfinite(inf(x)) && isfinite(sup(x))) ||
        throw(ArgumentError("expected a guaranteed, finite, nonempty real interval"))
    return x
end

"""
    input_interval(x::Union{Integer,Rational,AbstractString})

Enclose an exact integer, rational, or decimal/fraction point string in Float64.
Never pass decimal inputs through nearest floating-point parsing first.
Interval, decoration and uncertainty string syntax is intentionally unsupported.
Invalid, overflowing, and nonfinite inputs throw `ArgumentError`.
"""
input_interval(x::Union{Integer,Rational}) = _checked_interval(interval(Float64, x))
function input_interval(x::AbstractString)
    any(c -> c in "[]?_", x) && throw(ArgumentError("expected a numeric point string"))
    return _checked_interval(parse(Interval{Float64}, x))
end

const _BETA_TIMES = (0//1, 1//8, 3//8, 5//8, 7//8, 1//1)
const _BETA_POINTS = ((1//4, 0, -11//4, 0), (1//4, 0, -11//4, -1//4),
                      (1//4, 0, -9//4, -1//4), (1//4, 0, -9//4, 1//4),
                      (1//4, 0, -11//4, 1//4), (1//4, 0, -11//4, 0))
const _GAMMA_TIMES = (0//1, 1//16, 7//16, 29//64, 31//64, 33//64, 35//64,
                     9//16, 15//16, 1//1)
const _GAMMA_POINTS = ((1, 0, -10, 0), (1//4, 0, -10, 0), _BETA_POINTS...,
                      (1//4, 0, -10, 0), (1, 0, -10, 0))

function _loop_enclosure(t::Interval{T}, times, points) where {T<:AbstractFloat}
    _checked_interval(t)
    0 <= inf(t) <= sup(t) <= 1 || throw(ArgumentError("time interval must lie in [0,1]"))
    result = nothing
    for j in 1:length(times)-1
        segment = intersect_interval(t, interval(T, times[j], times[j+1]))
        isempty_interval(segment) && continue
        u = (segment - interval(T, times[j])) / interval(T, times[j+1]-times[j])
        image = ntuple(k -> interval(T, points[j][k]) +
                           u * interval(T, points[j+1][k]-points[j][k]), 4)
        result = isnothing(result) ? image : map(hull, result, image)
    end
    return result::NTuple{4,Interval{T}}
end

"""
    RationalLoop(times, points)

Exact piecewise-linear parameter loop. `times` are rational breakpoints from
exactly `0` to exactly `1`; `points` hold `(Re a, Im a, Re c, Im c)` at those
times. Breakpoints must strictly increase, the two sequences must have equal
length, and the loop must be EXACTLY closed. Continuity and closure are never
inferred from interval enclosures or samples; this exact data is what the
monodromy gate validates.
"""
struct RationalLoop
    times::Vector{Rational{BigInt}}
    points::Vector{NTuple{4,Rational{BigInt}}}
    function RationalLoop(times, points)
        t = [Rational{BigInt}(x) for x in times]
        all(x -> x isa Union{Tuple,AbstractVector} && length(x) == 4, points) ||
            throw(ArgumentError("each loop point needs four coordinates (Re a, Im a, Re c, Im c)"))
        p = [ntuple(k -> Rational{BigInt}(x[k]), 4) for x in points]
        length(t) == length(p) && length(t) >= 2 ||
            throw(ArgumentError("loop needs equally many breakpoints and points, at least two"))
        t[1] == 0 && t[end] == 1 || throw(ArgumentError("loop times must run from exactly 0 to exactly 1"))
        all(t[j] < t[j+1] for j in 1:length(t)-1) ||
            throw(ArgumentError("loop times must strictly increase"))
        p[1] == p[end] || throw(ArgumentError("loop must be exactly closed"))
        return new(t, p)
    end
end

const BETA_LOOP = RationalLoop(_BETA_TIMES, _BETA_POINTS)
const GAMMA_LOOP = RationalLoop(_GAMMA_TIMES, _GAMMA_POINTS)

"""
    loop_box(loop::RationalLoop, t::Interval{<:AbstractFloat})

CPU interval enclosure of the whole loop image over the time interval `t`,
splitting at every fold. Same input contract as `beta`/`gamma`.
"""
loop_box(loop::RationalLoop, t::Interval{T}) where {T<:AbstractFloat} =
    _loop_enclosure(t, loop.times, loop.points)

"""
    beta(t::Interval{<:AbstractFloat})

CPU interval enclosure of the paper's rectangular beta loop, with constant
`a = 1/4`. Returns `(real(a), imag(a), real(c), imag(c))`.
Splits at every fold and hulls all intersected segments. The guaranteed, finite,
nonempty time interval must be contained in `[0,1]`; invalid inputs throw.
This parameter enclosure is not proof that the loop is hyperbolic.
"""
beta(t::Interval{<:AbstractFloat}) = loop_box(BETA_LOOP, t)

"""
    gamma(t::Interval{<:AbstractFloat})

CPU enclosure of the paper's gamma loop based at `(a,c) = (1,-10)`, including
all folds of its beta segment. Same input/output contract and proof limitations
as `beta`.
"""
gamma(t::Interval{<:AbstractFloat}) = loop_box(GAMMA_LOOP, t)

include("sets_graphs.jl")
include("henon_data.jl")
include("cone_field.jl")
include("adaptive.jl")
include("hyperbolicity.jl")
include("monodromy.jl")

end
