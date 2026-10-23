# Validated parameter data and the common coverage radius. Shared by the uniform
# and the adaptive certification paths, so neither owns the other's definitions.

function _modulus_bounds(x, y)
    norm = _checked_interval(sqrt(x^2 + y^2))
    endpoints = ((Rational{BigInt}(inf(x)), Rational{BigInt}(sup(x))),
                 (Rational{BigInt}(inf(y)), Rational{BigInt}(sup(y))))
    lower2 = sum(max(0, lo, -hi)^2 for (lo, hi) in endpoints)
    upper2 = sum(max(lo^2, hi^2) for (lo, hi) in endpoints)
    lo, hi = Rational{BigInt}(inf(norm)), Rational{BigInt}(sup(norm))
    0 <= lo && lo^2 <= lower2 && hi^2 >= upper2 ||
        throw(ArgumentError("complex modulus enclosure failed exact endpoint checks"))
    return lo, hi
end

function _henon_data(p)
    _checked_image(p, 4)
    # ponytail: Float64 certificate bounds; parameterize the bound type if extreme-scale inputs are needed.
    parameters = map(x -> _checked_interval(interval(Float64, x)), p)
    ar, ai, cr, ci = parameters
    !(inf(ar) <= 0 <= sup(ar) && inf(ai) <= 0 <= sup(ai)) ||
        throw(ArgumentError("parameter box contains a=0; diffeomorphism theorem is unavailable"))
    _, a_upper = _modulus_bounds(ar, ai)
    c_lower, c_upper = _modulus_bounds(cr, ci)
    return (; parameters, a_upper, c_upper, c_lower)
end

function _henon_radius(data, requested)
    K = 1 + data.a_upper
    if isnothing(requested)
        k, c = interval(Float64, K), interval(Float64, data.c_upper)
        enclosure = _checked_interval((k + sqrt(k^2 + interval(4)*c)) / interval(2))
        r = sup(enclosure)
    else
        requested isa Union{Integer,Rational,AbstractFloat} || throw(ArgumentError("radius must be an exact numeric point"))
        r = sup(_checked_interval(interval(Float64, requested)))
    end
    q = Rational{BigInt}(r)
    q >= K && q^2 - K*q - data.c_upper >= 0 ||
        throw(ArgumentError("radius does not certify global chain-recurrent-set coverage"))
    return r
end

"""
    henon_radius(p)

Validated common complex-modulus radius from Lemma 11 of the paper. Accepts four
finite guaranteed CPU real intervals, outward-converts them to Float64, excludes
`a=0`, and verifies all modulus/radius bounds with exact rational endpoint checks.
Throws on invalid or unsupported inputs; does not by itself prove hyperbolicity.
"""
henon_radius(p) = _henon_radius(_henon_data(p), nothing)
