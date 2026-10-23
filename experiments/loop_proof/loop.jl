# Steps S0 and S1: the exact loop and the cover of its computed edge by closed pieces.
#
# a is fixed. c runs at times j/6, j = 0, ..., 6, through
#     c0 -> c0 + iT -> ct + iT -> ct -> ct - iT -> c0 - iT -> c0,
# so the requested point (a, ct) is at t = 1/2 and gamma(1 - t) = conj(gamma(t)).
# Only the right vertical edge c = ct + iu, 0 <= u <= T, is computed; the left
# and top edges lie in the HOV region and the lower half follows by conjugation.

"""
Loops with a proof run. Keys name the output directory; values are exact
rationals `(a, c0, ct, T)`.
"""
const LOOP_SPECS = Dict(
    "a-19_40_c-7_4" => (a=Q(-19, 40), c0=Q(-6), ct=Q(-7, 4), T=Q(4)),
    "a-1_c-7_2" => (a=Q(-1), c0=Q(-10), ct=Q(-7, 2), T=Q(29, 4)),
    "a-3_4_c-2" => (a=Q(-3, 4), c0=Q(-8), ct=Q(-2), T=Q(6)),
    "a51_80_c-7_2" => (a=Q(51, 80), c0=Q(-7), ct=Q(-7, 2), T=Q(17, 4)),
)

spec_dir(name) = joinpath(normpath(joinpath(@__DIR__, "..", "..")), "results", name)

"""
    symmetric_loop(spec)

The exact `RationalLoop` of `spec`, after checking with rational arithmetic:
closure and time order (`RationalLoop`); real basepoint in the DN region and
`|a| <= 1` (`_loop_geometry_check`); conjugate symmetry; and the HOV
condition `|c| > 2(1 + |a|)^2` on the left and top edges. Since
`c0 <= Re c <= ct < 0` there, `|c| >= |c0|` on the left edge and
`|c|^2 >= ct^2 + T^2` on the top edge, so checking those two numbers suffices.
"""
function symmetric_loop(spec)
    a, c0, ct, T = spec.a, spec.c0, spec.ct, spec.T
    c_corners = ((c0, Q(0)), (c0, T), (ct, T), (ct, Q(0)), (ct, -T), (c0, -T), (c0, Q(0)))
    points = [(a, Q(0), c[1], c[2]) for c in c_corners]
    loop = RationalLoop([Q(j, 6) for j in 0:6], points)
    require(OnLoops._loop_geometry_check(loop) == first(points), "basepoint check failed")
    conjugate(z) = (z[1], -z[2], z[3], -z[4])
    require(all(j -> points[8-j] == conjugate(points[j]), 1:7), "the loop must satisfy gamma(1-t) = conj(gamma(t))")
    hov_threshold = 2(1 + abs(a))^2
    require(c0 < ct < 0 && T > 0, "corners must satisfy c0 < ct < 0 and T > 0")
    require(c0^2 > hov_threshold^2, "left edge is not in the HOV region")
    require(ct^2 + T^2 > hov_threshold^2, "top edge is not in the HOV region")
    return loop
end

"""
    piece_parameters(spec, lo, hi)

The closed parameter box `a = spec.a`, `c = ct + iu` with `u in [lo, hi]`, as
outward-rounded intervals `(Re a, Im a, Re c, Im c)`.
"""
piece_parameters(spec, lo, hi) = (input_interval(spec.a), input_interval(0), input_interval(spec.ct),
                                  interval(Float64, lo, hi))

piece_tag(lo, hi, level) = "piece-$(numerator(lo))-$(denominator(lo))--$(numerator(hi))-$(denominator(hi))-L$(level)"

"""
A piece `(lo, hi, level)`: the parameter interval `u in [lo, hi]` and the grid
level (`2^level` cells per state axis).
"""
const Piece = Tuple{Q,Q,Int}

function require_contiguous(pieces, T)
    require(!isempty(pieces) && first(pieces)[1] == 0 && last(pieces)[2] == T,
            "pieces must start at u = 0 and end at u = T")
    require(all(i -> pieces[i][2] == pieces[i+1][1], 1:length(pieces)-1), "pieces must be contiguous")
end

"""
    initial_pieces(T)

Starting pieces for the search: width 1/128 on [0, 1/8] (level 7), 1/64 on
[1/8, 1] and 1/16 above (level 6).
"""
function initial_pieces(T)
    edges = vcat([Q(k, 128) for k in 0:15], [Q(k, 64) for k in 8:63], [Q(k, 16) for k in 16:floor(Int, 16T)])
    last(edges) == T || push!(edges, T)
    pieces = Piece[(edges[i], edges[i+1], edges[i] < Q(1, 8) ? 7 : 6) for i in 1:length(edges)-1]
    require_contiguous(pieces, T)
    return pieces
end

parts_path(dir) = joinpath(dir, "parts.tsv")

function read_pieces(dir)
    rows = split.(readlines(parts_path(dir))[2:end], '\t')
    return Piece[(parse(Q, r[1]), parse(Q, r[2]), parse(Int, r[3])) for r in rows]
end

function write_pieces(dir, pieces)
    open(parts_path(dir), "w") do io
        println(io, "imag_c_lo\timag_c_hi\tlevel")
        for (lo, hi, level) in pieces
            println(io, rational_text(lo), "\t", rational_text(hi), "\t", level)
        end
    end
end
