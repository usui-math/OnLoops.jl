export certify_monodromy, report_monodromy, monodromy_markdown

# Closed-cell contact: coordinatewise index distance <= 1, INCLUDING the identity
# offset, which is how the same cell continues across a time-slab boundary.
const _CONTACT_OFFSETS = Tuple{Int,Int,Int,Int}[
    Tuple(o) for o in Iterators.product(-1:1, -1:1, -1:1, -1:1)]

"""
    _dn_gate(base)

Exact Devaney-Nitecki test `D > 0 && D^2 > 20` for
`D = -4*Re(c)/(|Re(a)|+1)^2 - 5`, in rational arithmetic.
A rational lower bound of `2*sqrt(5)` must NOT be used on the right-hand side:
it accepts basepoints whose `D` is below `2*sqrt(5)`, for which `D^2 < 20`.
"""
function _dn_gate(base::NTuple{4,Rational{BigInt}})
    K2 = (abs(base[1]) + 1)^2
    D = -4*base[3]//K2 - 5
    return D > 0 && D*D > 20
end

function _loop_geometry_check(loop::RationalLoop)
    # Public vectors can change after construction; constructor validation alone
    # cannot justify the proof path's closure and time ordering.
    RationalLoop(loop.times, loop.points)
    base = loop.points[1]
    base[2] == 0 && base[4] == 0 ||
        throw(ArgumentError("Devaney-Nitecki basepoint must be an exact real parameter"))
    base[1] != 0 || throw(ArgumentError("basepoint must have a != 0"))
    # Convexity of the closed unit disk: vertex checks cover every linear segment.
    all(p -> p[1]^2 + p[2]^2 <= 1, loop.points) ||
        throw(ArgumentError("path must satisfy |a| <= 1 at every vertex"))
    _dn_gate(base) ||
        throw(ArgumentError("basepoint is outside the Devaney-Nitecki horseshoe region DN"))
    return base
end

function _even_dims(dims)
    d = dims isa Integer ? ntuple(_ -> dims, 4) : dims
    d isa Tuple && length(d) == 4 && all(j -> j isa Integer && 0 < j <= typemax(Int) && iseven(j), d) ||
        throw(ArgumentError("state partition must be four positive even integers (y=0 must be a grid boundary)"))
    return map(Int, d)
end

_slab_boxes(loop::RationalLoop, slabs::Int) =
    [loop_box(loop, interval(Float64, Rational{BigInt}(j-1, slabs), Rational{BigInt}(j, slabs)))
     for j in 1:slabs]

function _slab_cores(slab_boxes, dims, radius, max_vertices, max_edges)
    cells = prod(big.(dims))
    length(slab_boxes)*cells <= max_vertices ||
        throw(ArgumentError("slab candidates exceed max_vertices"))
    G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> radius, 4)), dims)
    source = GAIO.cover(G, :)
    K = keytype(typeof(G))
    cores = Vector{Vector{K}}(undef, length(slab_boxes))
    for k in eachindex(slab_boxes)
        g = outer_graph(z -> henon(z, slab_boxes[k]), source; max_vertices, max_edges)
        cores[k] = g.keys[graph_core(g.adjacency)]
        isempty(cores[k]) &&
            throw(ArgumentError("slab $k has an empty graph core; bounded orbits are not covered"))
    end
    return G, cores
end

"""
    _label_components(cores, grid)

Split (slab, key) vertices into connected components of the closed spacetime
prism: same-slab contacts and contacts between CONSECUTIVE slabs, both by
coordinatewise cell-index distance `<= 1`. Time 0 and time 1 are never glued.
Components meeting `Re y >= 0` at the first slab get label 0, those meeting
`Re y <= 0` get label 1; a component with both needs refinement. This is the
sign convention of the paper's partition pictures: digit 0 is the positive side.
"""
function _label_components(cores::Vector{<:AbstractVector}, grid::GAIO.BoxGrid)
    geometry = _grid_geometry(grid)
    s = length(cores)
    offsets = cumsum([0; length.(cores)])
    total = offsets[end]
    index = [Dict(key => offsets[k]+i for (i, key) in enumerate(cores[k])) for k in 1:s]
    parent = collect(1:total)
    function _find(x)
        while parent[x] != x
            parent[x] = parent[parent[x]]
            x = parent[x]
        end
        return x
    end
    function _join(a, b)
        ra, rb = _find(a), _find(b)
        ra == rb || (parent[max(ra, rb)] = min(ra, rb))
        return nothing
    end
    for k in 1:s, (i, key) in enumerate(cores[k]), offset in _CONTACT_OFFSETS
        neighbour = key .+ offset
        vertex = offsets[k]+i
        j = get(index[k], neighbour, 0)
        j == 0 || _join(vertex, j)
        if k < s
            m = get(index[k+1], neighbour, 0)
            m == 0 || _join(vertex, m)
        end
    end
    lower, step = geometry.lower[3], geometry.step[3]
    labels0, labels1 = falses(total), falses(total)
    for (i, key) in enumerate(cores[1])
        lo = lower + (Int(key[3])-1)*step
        root = _find(offsets[1]+i)
        lo + step >= 0 && (labels0[root] = true)
        lo <= 0 && (labels1[root] = true)
    end
    any(labels0) || any(labels1) ||
        throw(ArgumentError("no initial component is seeded by the Devaney-Nitecki half-planes"))
    collision = any(labels0 .& labels1)
    partitions = ntuple(s) do k
        k0, k1 = eltype(cores[k])[], eltype(cores[k])[]
        for (i, key) in enumerate(cores[k])
            root = _find(offsets[k]+i)
            labels0[root] && push!(k0, key)
            labels1[root] && push!(k1, key)
        end
        (k0, k1)
    end
    components = length(Set(_find(v) for v in 1:total))
    return (; collision, partitions, components, labels0, labels1, roots=[_find(v) for v in 1:total])
end

"""
    certify_monodromy(loop::RationalLoop; slabs=8, dims=8, max_refinements=3,
                      max_vertices=200_000, max_edges=2_000_000)

Certify the paper's §4 hypotheses for `loop` and compute disjoint labelled
partition enclosures by continuation. Status is `:proved` only when the exact
path, the DN basepoint, `|a| <= 1`, EVERY closed time-slab stage-3 certificate,
the full closed-box `K_p` enclosure, and the labelled-component separation all
hold. `:undetermined` covers uncertified slabs and unresolved collisions (at the
refinement cap, or when refining would exceed `max_vertices`); `:failed` covers
invalid paths, budgets exceeded by the requested configuration, failed slab
computations, and empty candidates. Never a claim of nontrivial monodromy.
Engineered with uniform closed grids, so the reachable resolution is limited.
"""
function certify_monodromy(loop::RationalLoop; slabs::Integer=8, dims=8,
                           max_refinements::Integer=3, max_vertices::Integer=200_000,
                           max_edges::Integer=2_000_000)
    result = (; status=:failed, reason="", slabs=0, dims=(0,0,0,0), radius=0.0,
              slab_boxes=nothing, partitions=nothing, components=0, collision=false)
    report(status, reason; extra...) = merge(result, (; status, reason, extra...))
    try
        slabs >= 1 || throw(ArgumentError("slabs must be a positive integer"))
        max_refinements >= 0 || throw(ArgumentError("max_refinements must be nonnegative"))
        max_vertices >= 0 && max_edges >= 0 ||
            throw(ArgumentError("graph budgets must be nonnegative"))
        s, d = Int(slabs), _even_dims(dims)
        s*prod(big.(d)) <= max_vertices || throw(ArgumentError("slab candidates exceed max_vertices"))
        _loop_geometry_check(loop)
        attempt = 0
        while true
            boxes = _slab_boxes(loop, s)
            certs = [certify_hyperbolicity(b; max_vertices, max_edges) for b in boxes]
            base = (; slabs=s, dims=d, slab_boxes=boxes)
            bad = findfirst(c -> c.status == :failed, certs)
            isnothing(bad) || return report(:failed, "slab $bad stage-3 computation failed: $(certs[bad].reason)"; base...)
            open = findfirst(c -> c.status == :undetermined, certs)
            isnothing(open) || return report(:undetermined, "slab $open is not certified: $(certs[open].reason)"; base...)
            radius = maximum(c -> c.radius, certs)
            grid, cores = _slab_cores(boxes, d, radius, max_vertices, max_edges)
            labels = _label_components(cores, grid)
            any(labels.labels0) && any(labels.labels1) ||
                throw(ArgumentError("initial candidates do not meet both Devaney-Nitecki half-planes"))
            found = (; radius, partitions=labels.partitions, components=labels.components,
                     collision=labels.collision)
            labels.collision || return report(:proved, "labelled partition enclosures are disjoint"; base..., found...)
            attempt < max_refinements ||
                return report(:undetermined, "labelled components still collide at the refinement cap"; base..., found...)
            next_s, next_d = 2s, 2 .* d
            next_s*prod(big.(next_d)) <= max_vertices ||
                return report(:undetermined, "labelled components still collide and refining would exceed max_vertices"; base..., found...)
            attempt += 1
            s, d = next_s, next_d
        end
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return report(:failed, sprint(showerror, e))
    end
end

# ---------------------------------------------------------------------------
# Candidate action report: continuation enclosures from a basepoint cover.
# This path assumes hyperbolicity; it never calls certify_hyperbolicity.
# ---------------------------------------------------------------------------

"""
    _keys_contact(A, B)

Closed-box contact of key collections in the same grid: coordinatewise index
distance `<= 1`, so face, edge and corner contact all count. Disjoint key SETS
are not geometric non-contact.
"""
function _keys_contact(A, B)
    isempty(A) && return false
    isempty(B) && return false
    neighbourhood = Set{eltype(B)}()
    for b in B, offset in _CONTACT_OFFSETS
        push!(neighbourhood, b .+ offset)
    end
    return any(a -> a in neighbourhood, A)
end

"""
    _classify_cylinder(cylinder_keys, q0, q1)

Classify one word from an enclosure `E_w` of the initial-partition cylinder and
enclosures `q_b` of the endpoint partitions `Q_b`. The inference is EXCLUSION of
the opposite label under the assumed two-partition `K = Q_0 + Q_1`; contact with
the wanted label alone proves nothing. An empty cylinder enclosure, or contact
with neither label, contradicts that assumption and is reported as
`:inconsistent`, never as a determined output.
"""
function _classify_cylinder(cylinder_keys, q0, q1)
    contact0 = _keys_contact(cylinder_keys, q0)
    contact1 = _keys_contact(cylinder_keys, q1)
    output = if isempty(cylinder_keys) || (!contact0 && !contact1)
        :inconsistent
    elseif contact0 && contact1
        :undetermined
    elseif contact0
        :label0
    else
        :label1
    end
    return (; contact0, contact1, output)
end

"""
    _cylinder_indices(adjacency, incoming, labels, memory, anticipation, word)

Vertices at symbolic time 0 that carry a graph path consistent with `word` over
the window `-memory, ..., 0, ..., anticipation`. `labels[v]` is the pair of
possible initial labels (`Re y >= 0` for digit 0, `Re y <= 0` for digit 1) of
vertex `v`. The forward half
is pulled back from symbolic time `+anticipation` and the backward half is pushed
forward from `-memory`, so both sets live at time 0. No path enumeration, and no
inverse-map integration for the negative symbolic times.
"""
function _cylinder_indices(adjacency, incoming, labels, memory, anticipation, word)
    L = memory + anticipation + 1
    length(word) == L || throw(DimensionMismatch("word length must equal memory + anticipation + 1"))
    allowed = (v, b) -> (b == 0 ? labels[v][1] : labels[v][2])
    forward = Set{Int}(v for v in 1:length(adjacency) if allowed(v, word[L]))
    for i in anticipation-1:-1:0
        need = word[memory+1+i]
        next = Set{Int}()
        for v in forward, u in incoming[v]
            allowed(u, need) && push!(next, u)
        end
        forward = next
    end
    backward = Set{Int}(v for v in 1:length(adjacency) if allowed(v, word[1]))
    for j in 2:memory+1
        need = word[j]
        next = Set{Int}()
        for v in backward, w in adjacency[v]
            allowed(w, need) && push!(next, w)
        end
        backward = next
    end
    return sort!(collect(intersect(forward, backward)))
end

"""
    report_monodromy(loop::RationalLoop; assume_hyperbolic=true, memory=1,
                     anticipation=1, slabs=8, dims=8, max_refinements=0,
                     max_words=1_048_576, max_vertices=200_000, max_edges=2_000_000)

Report the CANDIDATE action `rho = h1 o h0^{-1}` of the continuation on the
finite symbolic window `-memory, ..., 0, ..., anticipation`, using closed-box
continuation enclosures. `assume_hyperbolic=true` is REQUIRED: this entry assumes
the loop lies in the hyperbolic locus and never verifies hyperbolicity, so status
is `:candidate`, `:undetermined`, or `:failed` and NEVER `:proved`.

Word `w` is determined only by EXCLUDING the opposite endpoint label: with
`E_w` enclosing the initial cylinder `C_P(w)` and `Q_b_hat` enclosing the endpoint
partition `Q_b = T(P_b)`, `E_w` missing `Q_{1-b}_hat` gives `C_P(w)` inside `Q_b`
under the assumed two-partition. The inverse `h0 o T o h0^{-1}`, which is
`rho^{-1}`, is a different claim and is not reported.
All `2^(memory+anticipation+1)` words are reported in lexicographic order.

Endpoint enclosures come from the closed spacetime prism over `slabs` time slabs,
never from the basepoint image. A resource failure inside a refinement attempt
returns `:failed` without a table; rerun with `max_refinements=0` to keep the last
completely computed coarse table.
"""
function report_monodromy(loop::RationalLoop; assume_hyperbolic::Bool=false,
                          memory::Integer=1, anticipation::Integer=1, slabs::Integer=8,
                          dims=8, max_refinements::Integer=0, max_words::Integer=1_048_576,
                          max_vertices::Integer=200_000, max_edges::Integer=2_000_000)
    started = time_ns()
    result = (; status=:failed, reason="",
              claim="hyperbolicity is NOT verified; the report assumes the loop is hyperbolic and uses the basepoint coding",
              assume_hyperbolic, memory=0, anticipation=0, window=0, slabs=0, dims=(0,0,0,0),
              radius=0.0, base_parameter=nothing, words=nothing, table=nothing,
              base=(vertices=0, edges=0, core=0), start=(label0=0, label1=0),
              endpoint=(label0=0, label1=0), collision=false, components=0,
              seedless=(components=0, boxes=0), refinements=0,
              budgets=(; max_words, max_vertices, max_edges), environment=nothing)
    report(status, reason; extra...) = merge(result, (; status, reason,
        environment=(; julia=VERSION, threads=Threads.nthreads(),
                      seconds=(time_ns()-started)/1e9), extra...))
    try
        assume_hyperbolic ||
            throw(ArgumentError("report_monodromy requires assume_hyperbolic=true; it never verifies hyperbolicity"))
        memory >= 0 && anticipation >= 0 ||
            throw(ArgumentError("symbolic window bounds must be nonnegative integers"))
        slabs >= 1 || throw(ArgumentError("slabs must be a positive integer"))
        max_refinements >= 0 || throw(ArgumentError("max_refinements must be nonnegative"))
        max_words >= 0 && max_vertices >= 0 && max_edges >= 0 ||
            throw(ArgumentError("budgets must be nonnegative integers"))
        length_big = big(memory) + big(anticipation) + 1
        length_big <= 62 || throw(ArgumentError("symbolic window is too large to enumerate exactly"))
        m, n, L = Int(memory), Int(anticipation), Int(length_big)
        word_count = big(2)^L
        word_count <= max_words ||
            throw(ArgumentError("symbolic window needs $word_count words; max_words=$max_words"))
        # Lexicographic order: the first window position is the most significant bit.
        words = [ntuple(i -> (k >> (L - i)) & 1, L) for k in 0:Int(word_count)-1]
        base = _loop_geometry_check(loop)
        base_parameter = map(x -> input_interval(x), base)
        s, d = Int(slabs), _even_dims(dims)
        s*prod(big.(d)) <= max_vertices || throw(ArgumentError("slab candidates exceed max_vertices"))
        boxes = _slab_boxes(loop, s)
        r = maximum(_henon_radius(_henon_data(b), nothing) for b in boxes)
        r = max(r, _henon_radius(_henon_data(base_parameter), nothing))
        attempt = 0
        while true
            prod(big.(d)) <= max_vertices ||
                throw(ArgumentError("basepoint grid exceeds max_vertices"))
            G = GAIO.BoxGrid(GAIO.Box(ntuple(_ -> 0.0, 4), ntuple(_ -> r, 4)), d)
            g = outer_graph(z -> henon(z, base_parameter), GAIO.cover(G, :); max_vertices, max_edges)
            coreverts = graph_core(g.adjacency)
            isempty(coreverts) &&
                throw(ArgumentError("empty basepoint graph core; bounded orbits are not covered"))
            position = Dict(v => i for (i, v) in enumerate(coreverts))
            nodes = [Int[] for _ in coreverts]
            edges = 0
            for (i, v) in enumerate(coreverts), w in g.adjacency[v]
                j = get(position, w, 0)
                j == 0 || (push!(nodes[i], j); edges += 1)
            end
            incoming = _reverse_graph(nodes)
            corekeys = g.keys[coreverts]
            geometry = _grid_geometry(G)
            labels = ntuple(length(corekeys)) do i
                lo = geometry.lower[3] + (Int(corekeys[i][3])-1)*geometry.step[3]
                # Digit 0 is the positive half-plane, matching _label_components.
                (lo + geometry.step[3] >= 0, lo <= 0)
            end

            # Endpoint enclosures come from the CLOSED SPACETIME PRISM (time slabs),
            # never from the basepoint image, and time 0 is not glued to time 1.
            grid, cores = _slab_cores(boxes, d, r, max_vertices, max_edges)
            prism = _label_components(cores, grid)
            offsets = cumsum([0; length.(cores)])
            last = length(cores)
            q0 = [key for (i, key) in enumerate(cores[last]) if prism.labels0[prism.roots[offsets[last]+i]]]
            q1 = [key for (i, key) in enumerate(cores[last]) if prism.labels1[prism.roots[offsets[last]+i]]]
            !isempty(q0) && !isempty(q1) ||
                throw(ArgumentError("an endpoint label enclosure is empty; the nonempty two-partition assumption is contradicted"))
            start0 = count(i -> prism.labels0[prism.roots[i]], 1:length(cores[1]))
            start1 = count(i -> prism.labels1[prism.roots[i]], 1:length(cores[1]))
            allroots = unique(prism.roots)
            seedless = [root for root in allroots
                        if !prism.labels0[root] && !prism.labels1[root]]
            seedless_set = Set(seedless)
            seedless_boxes = count(root -> root in seedless_set, prism.roots)

            table = map(words) do word
                cylinder = corekeys[_cylinder_indices(nodes, incoming, labels, m, n, word)]
                merge((; word, boxes=length(cylinder)), _classify_cylinder(cylinder, q0, q1))
            end
            undetermined = count(e -> e.output == :undetermined, table)
            inconsistent = count(e -> e.output == :inconsistent, table)
            found = (; memory=m, anticipation=n, window=L, slabs=s, dims=d, radius=r,
                     base_parameter, words, table,
                     base=(vertices=length(g.keys), edges=sum(length, g.adjacency),
                           core=length(coreverts), core_edges=edges),
                     start=(label0=start0, label1=start1),
                     endpoint=(label0=length(q0), label1=length(q1)),
                     collision=prism.collision, components=prism.components,
                     seedless=(components=length(seedless), boxes=seedless_boxes),
                     refinements=attempt)
            inconsistent > 0 && return report(:failed,
                "$inconsistent of $(length(words)) cylinder enclosures are empty or miss both endpoint labels, " *
                "contradicting the assumed full two-shift; no word is silently dropped"; found...)
            undetermined == 0 && return report(:candidate,
                "every word of the window is determined by opposite-label exclusion; hyperbolicity is assumed, not verified"; found...)
            next_d = 2 .* d
            if attempt >= max_refinements
                return report(:undetermined,
                    "$undetermined of $(length(words)) words are unresolved at the refinement cap"; found...)
            end
            length(boxes)*prod(big.(next_d)) <= max_vertices ||
                return report(:undetermined,
                    "$undetermined of $(length(words)) words are unresolved and refining would exceed max_vertices"; found...)
            attempt += 1
            d = next_d
        end
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return report(:failed, sprint(showerror, e))
    end
end

"""
    monodromy_markdown(report)

Render the structured report as a UTF-8 Markdown table. It only formats an
already computed report: no new numerical work, and no claim beyond `report.status`.
"""
function monodromy_markdown(r)
    r.table === nothing && return ""
    io = IOBuffer()
    println(io, "# Candidate report of the monodromy action")
    println(io)
    println(io, "- Claim: ", r.claim)
    println(io, "- Status: `", r.status, "` — ", r.reason)
    println(io, "- Convention: `rho = h1 ∘ h0^(-1)`, label 0 is `Re y > 0`, label 1 is `Re y < 0`,")
    println(io, "  words are ordered `-m, ..., 0, ..., n` (m=", r.memory, ", n=", r.anticipation, ")")
    println(io, "- Settings: ", 2^r.window, " words, grid ", r.dims, ", slabs ", r.slabs,
            ", radius ", r.radius, ", ", r.refinements, " refinements")
    println(io, "- Budgets: ", r.budgets)
    println(io, "- Basepoint: ", r.base_parameter)
    println(io, "- Diagnostics: basepoint graph ", r.base, " / start labels ", r.start, " / end labels ", r.endpoint,
            " / collisions ", r.collision, " / seedless components ", r.seedless)
    println(io, "- Environment: Julia ", r.environment.julia, ", threads ", r.environment.threads,
            ", ", round(r.environment.seconds; digits=2), " s")
    println(io)
    println(io, "| Word (", -r.memory, "..", r.anticipation, ") | Cylinder enclosure boxes | Touches 0 | Touches 1 | Report |")
    println(io, "| --- | --- | --- | --- | --- |")
    for entry in r.table
        label = entry.output == :label0 ? "output 0 (opposite label excluded)" :
                entry.output == :label1 ? "output 1 (opposite label excluded)" :
                entry.output == :undetermined ? "unresolved (touches both labels)" : "consistency failure"
        println(io, "| ", join(entry.word, ""), " | ", entry.boxes, " | ",
                entry.contact0 ? "yes" : "no", " | ", entry.contact1 ? "yes" : "no",
                " | ", label, " |")
    end
    return String(take!(io))
end
