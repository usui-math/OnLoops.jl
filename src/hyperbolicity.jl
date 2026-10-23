export henon_radius, fiber_isolated, certify_hyperbolicity, certify_adaptive

function _positive_dims(dims, n)
    dims isa Tuple && length(dims) == n || throw(DimensionMismatch("partition dimension must be $n"))
    all(j -> j isa Integer && 0 < j <= typemax(Int), dims) || throw(ArgumentError("partition sizes must be positive bounded integers"))
    return map(Int, dims)
end

function _base_x_minimum(base::GAIO.BoxSet)
    geometry = _grid_geometry(base.partition)
    length(geometry.dims) == 4 || throw(DimensionMismatch("Hénon base dimension must be four"))
    isempty(base.set) && throw(ArgumentError("empty global recurrent candidate is a consistency failure"))
    return minimum(base.set) do key
        _checked_key(geometry.dims, key)
        sum(1:2) do k
            lo = geometry.lower[k] + (Int(key[k])-1)*geometry.step[k]
            hi = lo + geometry.step[k]
            max(0, lo, -hi)^2
        end
    end
end

"""
    fiber_isolated(boxes::GAIO.BoxSet; base_dimension)

Check strict fiber-only interior in the canonical grid domain. For a uniform
closed cell this is exactly `1 < key[k] < dims[k]` for every fiber axis. Empty
sets return false. This is ONLY a geometric predicate: it does not certify the
cover, invariance, zero-section inclusion, or hyperbolicity on its own.
"""
function fiber_isolated(boxes::GAIO.BoxSet; base_dimension)
    geometry = _grid_geometry(boxes.partition)
    n = length(geometry.dims)
    base_dimension isa Integer && 0 < base_dimension < n || throw(ArgumentError("invalid base dimension"))
    foreach(key -> _checked_key(geometry.dims, key), boxes.set)
    return !isempty(boxes.set) && all(1 < key[k] < geometry.dims[k]
                                   for key in boxes.set for k in base_dimension+1:n)
end

"""
    certify_hyperbolicity(p; radius=nothing, base_dims=(4,4,4,4),
                         fiber_dims=(4,4,4,4), max_vertices=100_000,
                         max_edges=1_000_000)

Certify hyperbolicity on the ACTUAL global chain recurrent set for every fixed
parameter in a validated interval box. Status is `:proved`, `:undetermined`, or
`:failed`, NEVER a claim of nonhyperbolicity. The method records a global, base,
or adaptive-lattice bounded-tangent-orbit dominance proof, or a complete
conservative tangent graph with strict relative fiber isolation. The latter uses
unit fiber domain [-1,1]^4. The adaptive step runs with its own default lattice
budget; `certify_adaptive` exposes that budget directly.
Skipped candidate sets are `nothing`; returned sets are inspectable data, not
trusted proof tokens. Invalid/incomplete computations fail; unexpected exceptions
and interrupts propagate.
"""
function certify_hyperbolicity(p; radius=nothing, base_dims=(4,4,4,4),
                              fiber_dims=(4,4,4,4), max_vertices=100_000,
                              max_edges=1_000_000, cone_dims=(8,4), cone_iterations=1200)
    parameters, r, base, tangent, cone = nothing, nothing, nothing, nothing, nothing
    method = :validation
    report(status, reason) = (; status, method, reason, parameters, radius=r, base, tangent, cone)
    try
        bdims, fdims = _positive_dims(base_dims, 4), _positive_dims(fiber_dims, 4)
        max_vertices isa Integer && max_edges isa Integer && max_vertices >= 0 && max_edges >= 0 ||
            throw(ArgumentError("graph budgets must be nonnegative integers"))
        data = _henon_data(p)
        parameters = data.parameters
        r = _henon_radius(data, radius)
        K, R = 1 + data.a_upper, Rational{BigInt}(r)
        # On actual recurrent orbits |X|,|y| <= R by Lemma 11, NOT just cube membership.
        # Bounded tangent v obeys 2|x_n||v_n| <= (1+|a|)sup|v|; strict dominance excludes it.
        if 4*(data.c_lower-K*R) > K^2
            method = :global_dominance
            return report(:proved, "global modulus bounds exclude all nonzero bounded tangent orbits")
        end

        method = :base_graph
        prod(big.(bdims)) <= max_vertices || throw(ArgumentError("base grid exceeds max_vertices"))
        G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> r, 4)), bdims)
        bg = outer_graph(z -> henon(z, parameters), GAIO.cover(G, :); max_vertices, max_edges)
        base = GAIO.BoxSet(G, Set(bg.keys[recurrent_vertices(bg.adjacency)]))
        isempty(base.set) && throw(ArgumentError("empty global recurrent candidate contradicts fixed-point existence"))
        if 4*_base_x_minimum(base) > K^2
            method = :base_dominance
            return report(:proved, "complete base recurrence cover excludes all nonzero bounded tangent orbits")
        end

        # A real-state certificate cannot cover nonreal bounded base orbits, even
        # when all parameter coordinates are real. Only the complex-state path is
        # eligible for promotion to this global certificate.
        method = :cone_field
        cone = certify_cone_field(p; radius=r, dims=cone_dims, iterations=cone_iterations,
                                  max_vertices, max_edges)
        cone.status == :proved && cone.scope == :complex_state && return report(:proved, cone.reason)

        # Uniform refinement need not improve this bound while an origin cell
        # survives; adaptive refinement can remove such cells without losing coverage.
        adaptive = _adaptive_refine(_base_fixed_boxes(base), _base_fixed_scales(base),
                                    parameters, r, K)
        if adaptive.status == :proved
            method = :adaptive_base_dominance
            return report(:proved, adaptive.reason)
        end

        method = :tangent_graph
        count = big(length(base.set))*prod(big.(fdims))
        count <= max_vertices || throw(ArgumentError("initial tangent cover exceeds max_vertices"))
        TG = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 8),
                                 (ntuple(_ -> r, 4)..., 1.0, 1.0, 1.0, 1.0)), (bdims..., fdims...))
        initial = Set{NTuple{8,Int}}()
        for key in base.set, fiber in CartesianIndices(fdims)
            push!(initial, (key..., Tuple(fiber)...))
        end
        tg = outer_graph(zv -> tangent_lift(zv, parameters), GAIO.BoxSet(TG, initial); max_vertices, max_edges)
        tangent = GAIO.BoxSet(TG, Set(tg.keys[graph_core(tg.adjacency)]))
        isempty(tangent.set) && throw(ArgumentError("empty global tangent candidate contradicts zero-section coverage"))
        if fiber_isolated(tangent; base_dimension=4)
            return report(:proved, "complete tangent graph certifies strict relative fiber isolation")
        end
        return report(:undetermined, "complete tangent candidate still touches the fiber boundary")
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return report(:failed, sprint(showerror, e))
    end
end
