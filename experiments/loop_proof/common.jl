# Imports and small helpers shared by every step of the symmetric-loop proof.
using OnLoops
using IntervalArithmetic: interval, inf, sup, intersect_interval, isempty_interval,
                          isnai, isguaranteed, hull, nai
import GAIO

const Q = Rational{BigInt}

"""
A state box `(Re x, Im x, Re y, Im y)` of four closed Float64 intervals.
"""
const StateBox = NTuple{4,typeof(input_interval(0))}

"""
    require(condition, message)

Throw `ArgumentError(message)` unless `condition` holds. Every proof condition
uses this instead of `@assert`, which Julia may disable at some optimisation levels.
"""
require(condition::Bool, message::AbstractString) = condition || throw(ArgumentError(message))

"""
    rational_text(q)

Exact text `p/q` of a rational number (integers too, e.g. `5/1`).
"""
rational_text(q) = string(numerator(q), "/", denominator(q))

"""
    exact_endpoints(box)

Each interval of `box` as its exact rational endpoints `(lo, hi)`.
"""
exact_endpoints(box) = map(I -> (Q(inf(I)), Q(sup(I))), box)

"""
    is_valid_interval(I)

True when `I` is a guaranteed, finite, nonempty closed interval.
"""
is_valid_interval(I) = isguaranteed(I) && !isnai(I) && !isempty_interval(I) &&
                       isfinite(inf(I)) && isfinite(sup(I))

"""
    state_grid(radius, n)

The uniform grid of `[-radius, radius]^4` with `n` cells per axis.
"""
state_grid(radius, n) = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> radius, 4)),
                                     ntuple(_ -> n, 4))

"""
    induced_subgraph(adjacency, kept)

Adjacency lists of the subgraph on the sorted vertex list `kept`, with the kept
vertices renumbered `1:length(kept)` in order. Edge order is preserved.
"""
function induced_subgraph(adjacency, kept)
    position = Dict(v => i for (i, v) in enumerate(kept))
    return [[position[w] for w in adjacency[v] if haskey(position, w)] for v in kept]
end
