export certify_cone_field, certify_real_cone_field

const _ConeRational = Rational{BigInt}

function _cone_quad_extrema(c2::_ConeRational, c1::_ConeRational, c0::_ConeRational,
                            lo::_ConeRational, hi::_ConeRational)
    if c2 == 0
        vlo, vhi = c1*lo + c0, c1*hi + c0
        return min(vlo, vhi), max(vlo, vhi)
    end
    vlo, vhi = c2*lo^2 + c1*lo + c0, c2*hi^2 + c1*hi + c0
    vx = -c1/(2c2)
    if lo < vx < hi
        vv = c2*vx^2 + c1*vx + c0
        return c2 > 0 ? (vv, max(vlo, vhi)) : (min(vlo, vhi), vv)
    end
    return min(vlo, vhi), max(vlo, vhi)
end

"""
    _cone_edge_margin(Qk, Qj, alo, ahi, xl, xh; xsub, asub)

Rigorous lower bound of the smallest eigenvalue of
`A(x,a) = M(x,a)' Q_j M(x,a) - Q_k` over `x` in `[xl,xh]` and `a` in `[alo,ahi]`,
in exact rational arithmetic, for the real slice. Its entries are

    a11(x)   = 4 p_j x^2 + 4 q_j x + (r_j - p_k)     (x only)
    a22(a)   = p_j a^2 - r_k                         (a only)
    a12(x,a) = -2 p_j a x - q_j a - q_k              (bilinear)
    det      = a11 a22 - a12^2                       (interval bound, subdivided)

`a11 > 0`, `a22 > 0`, `det > 0` imply both eigenvalues are positive and
`lam_min = det/lam_max >= det/tr`. This is a lower bound, never a sample.
"""
function _cone_edge_margin(Qk::Matrix{_ConeRational}, Qj::Matrix{_ConeRational},
                           alo::_ConeRational, ahi::_ConeRational,
                           xl::_ConeRational, xh::_ConeRational;
                           xsub::Int=16, asub::Int=6)
    pj, qj, rj = Qj[1, 1], Qj[1, 2], Qj[2, 2]
    pk, qk, rk = Qk[1, 1], Qk[1, 2], Qk[2, 2]
    # A point parameter needs no a-subdivision: every sub-box would be identical.
    asub = alo == ahi ? 1 : asub
    lo11, hi11 = _cone_quad_extrema(4pj, 4qj, rj - pk, xl, xh)
    lo22, hi22 = _cone_quad_extrema(pj, zero(pj), -rk, alo, ahi)
    trhi = hi11 + hi22
    (lo11 <= 0 || lo22 <= 0 || trhi <= 0) && return min(lo11, lo22)
    c4pj = interval(Float64, 4pj)
    c4qj = interval(Float64, 4qj)
    cr = interval(Float64, rj - pk)
    cpj = interval(Float64, pj)
    crk = interval(Float64, rk)
    c2pj = interval(Float64, 2pj)
    cqj = interval(Float64, qj)
    cqk = interval(Float64, qk)
    xstep = (xh - xl)//xsub
    astep = (ahi - alo)//asub
    detlow = _ConeRational(-1)
    for i in 0:xsub-1, m in 0:asub-1
        X = hull(interval(Float64, xl + i*xstep), interval(Float64, xl + (i + 1)*xstep))
        Aa = hull(interval(Float64, alo + m*astep), interval(Float64, alo + (m + 1)*astep))
        a11 = c4pj*X^2 + c4qj*X + cr
        a22 = cpj*Aa^2 - crk
        a12 = -c2pj*Aa*X - cqj*Aa - cqk
        d = _ConeRational(inf(a11*a22 - a12^2))
        i == 0 && m == 0 && (detlow = d)
        detlow = min(detlow, d)
    end
    detlow <= 0 && return min(lo11, lo22, detlow)
    return min(lo11, lo22, detlow//trhi)
end

# Smallest eigenvalue and eigenvector of a symmetric 2x2 matrix in closed form:
# the search loop evaluates this millions of times, so no eigendecomposition.
function _cone_mineig(a, b, c)
    tr = a + c
    disc = sqrt(max((a - c)^2 + 4b*b, 0.0))
    lam = 0.5*(tr - disc)
    if abs(b) > 1e-300
        u = (b, lam - a)
        nrm = sqrt(u[1]^2 + u[2]^2)
        return lam, (u[1]/nrm, u[2]/nrm)
    end
    return a <= c ? (a, (1.0, 0.0)) : (c, (0.0, 1.0))
end

# Projected subgradient ascent on the concave objective
#     min over edges and samples of lam_min(M(x,a)'Q_jM(x,a) - Q_k)
# over the convex set max_k ||Q_k||_F <= 1, starting from the uniform solution
# Q = diag(1,-a) that is feasible on |x| > (1+a)/2. Deterministic.
function _cone_search(edges, alo, ahi, ncells; iterations::Int=2000, samples::Int=2)
    amid = (alo + ahi)/2
    as = samples == 0 ? (amid,) : ntuple(i -> alo + (ahi - alo)*i/samples, samples + 1)
    Q = [Matrix{Float64}([1.0 0.0; 0.0 -amid]) for _ in 1:ncells]
    best, bestQ = -Inf, deepcopy(Q)
    for it in 1:iterations
        worst, wk, wj, wx, wa, wu = Inf, 0, 0, 0.0, amid, (0.0, 0.0)
        for (k, j, xl, xh) in edges
            for t in 0:samples
                x = xl + (xh - xl)*t/samples
                for a in as
                    M = [2x -a; 1.0 0.0]
                    A = M'*Q[j]*M - Q[k]
                    lam, u = _cone_mineig(A[1, 1], A[1, 2], A[2, 2])
                    lam < worst && ((worst, wk, wj, wx, wa, wu) = (lam, k, j, x, a, u))
                end
            end
        end
        worst > best && ((best, bestQ) = (worst, deepcopy(Q)))
        best > 1e-7 && break
        M = [2wx -wa; 1.0 0.0]
        u = [wu[1], wu[2]]
        sv = 0.5/sqrt(it)
        Q[wj] .+= sv .* (M*u*u'*M')
        Q[wk] .-= sv .* (u*u')
        for k in 1:ncells
            Q[k] = (Q[k] + Q[k]')/2
            nr = sqrt(sum(abs2, Q[k]))
            nr > 1 && (Q[k] ./= nr)
        end
    end
    return best, bestQ
end

# Real parameters preserve the real plane; they do not constrain complex orbits.
function _cone_real_slice(parameters)
    ar, ai, cr, ci = parameters
    (inf(ai) == 0 == sup(ai)) || return nothing
    (inf(ci) == 0 == sup(ci)) || return nothing
    return (_ConeRational(inf(ar)), _ConeRational(sup(ar)))
end

function _henon_real_slice(z, p)
    x, y = z
    zero_interval = interval(Float64, 0)
    image = henon((x, zero_interval, y, zero_interval), p)
    return (image[1], image[3])
end

"""
    certify_real_cone_field(p; radius=nothing, dims=(48,48), iterations=2500,
                            samples=2, max_vertices=400_000, max_edges=20_000_000)

Certify the absence of nonzero bounded two-sided tangent orbits over REAL bounded
base orbits. Real parameters preserve this plane but may also have nonreal bounded
orbits; this result must never be promoted to global complex hyperbolicity.
The result always carries `scope=:real_state`. A numerical search constructs the
forms; only the rational/interval check on every core transition decides success.
With uniformly bounded forms, summing the strict increasing inequality over both
ends gives square summability. Then q tends to zero at both ends; monotonicity
makes q identically zero and the strict increment makes the tangent orbit zero.
"""
function certify_real_cone_field(p; radius=nothing, dims=(48, 48), iterations::Integer=2500,
                            samples::Integer=2, max_vertices::Integer=400_000,
                            max_edges::Integer=20_000_000)
    result = (; status=:failed, reason="", method=:cone_field, scope=:real_state, parameters=nothing,
              radius=0.0, dims=(0, 0), cells=0, edges=0, core=0,
              sampled_margin=-Inf, margin=_ConeRational(-1), iterations=0)
    report(status, reason; extra...) = merge(result, (; status, reason, extra...))
    try
        1 <= iterations <= typemax(Int) && 1 <= samples <= typemax(Int) ||
            throw(ArgumentError("cone search needs bounded iterations >= 1 and samples >= 1"))
        max_vertices >= 0 && max_edges >= 0 ||
            throw(ArgumentError("graph budgets must be nonnegative"))
        dims isa Tuple && length(dims) == 2 && all(d -> d isa Integer && 0 < d <= typemax(Int), dims) ||
            throw(ArgumentError("cone grid needs two positive integer sizes"))
        d = map(Int, dims)
        data = _henon_data(p)
        slice = _cone_real_slice(data.parameters)
        isnothing(slice) && return report(:undetermined,
            "cone field certificate requires real parameters (Im a = Im c = 0); complex boxes are not implemented",
            parameters=data.parameters)
        alo, ahi = slice
        r = _henon_radius(data, radius)
        prod(big.(d)) <= max_vertices || throw(ArgumentError("cone grid exceeds max_vertices"))
        budget = (; parameters=data.parameters, radius=r, dims=d, iterations=Int(iterations))
        G = GAIO.BoxGrid(GAIO.Box((0.0, 0.0), (r, r)), d)
        g = outer_graph(z -> _henon_real_slice(z, data.parameters), GAIO.cover(G, :);
                        max_vertices, max_edges)
        core = graph_core(g.adjacency)
        isempty(core) && throw(ArgumentError("empty graph core; bounded orbits are not covered"))
        position = Dict(v => i for (i, v) in enumerate(core))
        geometry = _grid_geometry(G)
        edges = Tuple{Int,Int,Float64,Float64}[]
        for v in core
            lo = geometry.lower[1] + (Int(g.keys[v][1]) - 1)*geometry.step[1]
            for w in g.adjacency[v]
                j = get(position, w, 0)
                j == 0 && continue
                push!(edges, (Int(g.keys[v][1]), Int(g.keys[w][1]), Float64(lo),
                              Float64(lo + geometry.step[1])))
            end
        end
        isempty(edges) && throw(ArgumentError("no core edge to certify"))
        sort!(unique!(edges))
        ncells = maximum(max(k, j) for (k, j, _, _) in edges)
        best, Q = _cone_search(edges, Float64(alo), Float64(ahi), ncells;
                               iterations=Int(iterations), samples=Int(samples))
        Qr = [map(_ConeRational, Q[k]) for k in 1:ncells]
        margin = _ConeRational(-1)
        for (i, (k, j, _, _)) in enumerate(edges)
            lo = geometry.lower[1] + (k - 1)*geometry.step[1]
            m = _cone_edge_margin(Qr[k], Qr[j], alo, ahi, lo, lo + geometry.step[1])
            i == 1 && (margin = m)
            margin = min(margin, m)
        end
        found = (; cells=length(core), edges=length(edges), core=length(core),
                 sampled_margin=best, margin=margin, width=Float64(geometry.step[1]))
        margin > 0 && return report(:proved,
            "cellwise strict cone condition holds with margin $(Float64(margin)) on all " *
            "$(length(edges)) core edges at x-cell width $(Float64(geometry.step[1]))";
            budget..., found...)
        return report(:undetermined,
            "no cellwise form family with a positive rigorous margin at this resolution " *
            "(sampled $(round(best; digits=7)), rigorous $(Float64(margin)))"; budget..., found...)
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return report(:failed, sprint(showerror, e))
    end
end

# A fixed complex a still gives a separable quadratic in the two x coordinates;
# expanding it avoids dependency overestimation from interval products.
const _ConeParameter = Union{_ConeRational,Complex{_ConeRational}}
function _cone_radial_extrema(c, d, e, f, box)
    u0,u1,v0,v1 = box
    lo_u,hi_u = _cone_quad_extrema(c,d,zero(c),u0,u1)
    lo_v,hi_v = _cone_quad_extrema(c,e,zero(c),v0,v1)
    return lo_u+lo_v+f,hi_u+hi_v+f
end

function _cone_hermitian_bounds(src, dst, a::_ConeParameter, box::NTuple{4,_ConeRational})
    P,γ,δ,R = src
    p,α,β,r = dst
    B = abs2(a)*p-R
    lo11,hi11 = _cone_radial_extrema(4p,4α,4β,r-P,box)
    h = a*complex(α,-β)+complex(γ,δ)
    t = a*conj(h)
    C = -4p*R
    D = 4*(B*α-p*real(t))
    E = 4*(B*β-p*imag(t))
    F = B*(r-P)-abs2(h)
    detlo,dethi = _cone_radial_extrema(C,D,E,F,box)
    return (; a11_min=lo11,a11_max=hi11,a22=B,determinant_min=detlo,
             determinant_max=dethi,trace_max=hi11+B,coefficients=(C,D,E,F))
end

function _cone_hermitian_margin(src, dst, a::_ConeParameter, box::NTuple{4,_ConeRational})
    b = _cone_hermitian_bounds(src,dst,a,box)
    if b.a11_min <= 0 || b.a22 <= 0 || b.determinant_min <= 0
        return min(b.a11_min,b.a22,b.determinant_min,zero(real(a)))
    end
    return b.determinant_min/b.trace_max
end

# The full a rectangle is covered by a rational perturbation bound; sampling its
# centre alone would not verify the interval cocycle.
function _cone_parameter_margin(src, dst, a::_ConeParameter,
                                deviation::_ConeRational, box::NTuple{4,_ConeRational})
    deviation >= 0 || throw(ArgumentError("parameter deviation must be nonnegative"))
    centre_margin = _cone_hermitian_margin(src,dst,a,box)
    iszero(deviation) && return centre_margin
    xnorm = max(abs(box[1]),abs(box[2]))+max(abs(box[3]),abs(box[4]))
    mnorm = 2xnorm+abs(real(a))+abs(imag(a))+1
    qnorm = max(abs(dst[1]),abs(dst[4]))+abs(dst[2])+abs(dst[3])
    return centre_margin-qnorm*(2mnorm*deviation+deviation^2)
end

function _cone_parameter_enclosure(parameters)
    endpoints = [( _ConeRational(inf(p)), _ConeRational(sup(p)) ) for p in parameters[1:2]]
    centre = complex((endpoints[1][1]+endpoints[1][2])/2,
                     (endpoints[2][1]+endpoints[2][2])/2)
    deviation = sum((hi-lo)/2 for (lo,hi) in endpoints)
    return centre,deviation
end

function _cone_complex_matrix(src,dst,x,a)
    P,γ,δ,R = src
    p,α,β,r = dst
    a11 = 4p*abs2(x)+4*(α*real(x)+β*imag(x))+r-P
    a12 = -2a*p*conj(x)-a*complex(α,-β)-complex(γ,δ)
    a22 = abs2(a)*p-R
    return a11,a12,a22
end

function _cone_complex_eigen(a11,a12,a22)
    disc = sqrt((a11-a22)^2+4abs2(a12))
    lam = (a11+a22-disc)/2
    if abs(a12) > 1e-300
        # Either row yields an eigenvector; use the larger one to avoid cancellation.
        if abs(lam-a11) >= abs(lam-a22)
            u,v = a12,complex(lam-a11)
        else
            u,v = complex(lam-a22),conj(a12)
        end
        nr = sqrt(abs2(u)+abs2(v))
        return lam,u/nr,v/nr
    end
    return a11 <= a22 ? (a11,1.0+0im,0.0+0im) : (a22,0.0+0im,1.0+0im)
end

# Single-edge projected subgradient step for the complex search: the tangent
# image of the violating eigenvector gives a rank-one Hermitian update.
function _cone_update(q,u,v,scale)
    s = u*conj(v)
    return (q[1]+scale*abs2(u),q[2]+scale*real(s),
            q[3]+scale*imag(s),q[4]+scale*abs2(v))
end

function _cone_normalize(q)
    nr = sqrt(q[1]^2+2q[2]^2+2q[3]^2+q[4]^2)
    return nr > 1 ? map(x->x/nr,q) : q
end

function _cone_verify_family(forms, pairs, a, boxes; deviation=zero(real(a)))
    return minimum(_cone_parameter_margin(forms[k],forms[j],a,deviation,boxes[k]) for (k,j) in pairs)
end

# Numerical samples only construct a witness. Exact checks on every projected
# transition decide acceptance; positive samples alone never end the search.
function _cone_search_complex(pairs, boxes, a::_ConeParameter;
                              iterations::Int,samples::Int,initial_forms=nothing,
                              deviation::_ConeRational=zero(real(a)))
    af = iszero(imag(a)) ? Float64(real(a)) : ComplexF64(a)
    n = length(boxes)
    Q = isnothing(initial_forms) ? fill((1.0,0.0,0.0,-abs(af)),n) : copy(initial_forms)
    length(Q) == n || throw(DimensionMismatch("initial forms must match the x cells"))
    all(q -> length(q)==4 && all(isfinite,q),Q) || throw(ArgumentError("forms must be finite"))
    Q = _cone_normalize.(Q)
    sample_points = map(boxes) do box
        u0,u1,v0,v1 = Float64.(box)
        [complex(u0+(u1-u0)*i/samples,v0+(v1-v0)*j/samples)
         for i in 0:samples for j in 0:samples]
    end
    best,bestQ = -Inf,copy(Q)
    lastcheck = 0
    for it in 1:iterations
        worst,wk,wj,wx,wu,wv = Inf,0,0,0.0+0im,0.0+0im,0.0+0im
        for (k,j) in pairs, x in sample_points[k]
            A = _cone_complex_matrix(Q[k],Q[j],x,af)
            lam,u,v = _cone_complex_eigen(A...)
            if lam < worst
                worst,wk,wj,wx,wu,wv = lam,k,j,x,u,v
            end
        end
        if worst > best
            best,bestQ = worst,copy(Q)
        end
        if worst > 0 && (lastcheck == 0 || it-lastcheck >= 25 || it == iterations)
            exact = [map(_ConeRational,q) for q in Q]
            margin = _cone_verify_family(exact,pairs,a,boxes;deviation)
            lastcheck = it
            margin > 0 && return (; forms=exact,margin,sampled=worst,iterations=it)
        end
        sv = 0.5/sqrt(it)
        Q[wj] = _cone_update(Q[wj],2wx*wu-af*wv,wu,sv)
        Q[wk] = _cone_update(Q[wk],wu,wv,-sv)
        Q[wj] = _cone_normalize(Q[wj])
        Q[wk] = _cone_normalize(Q[wk])
    end
    exact = [map(_ConeRational,q) for q in bestQ]
    return (; forms=exact,margin=_cone_verify_family(exact,pairs,a,boxes;deviation),
             sampled=best,iterations)
end

"""
    certify_cone_field(p; radius=nothing, dims=(48,8), iterations=4000,
                       samples=3, max_vertices=400_000, max_edges=20_000_000,
                       initial_forms=nothing)

Certify the global COMPLEX chain recurrent set with Hermitian quadratic forms on
complex x cells. The complete four-real-dimensional base graph uses dimensions
`(dims[1],dims[1],dims[2],dims[2])`, including for real parameter boxes. Both a and c
may be complex rectangular parameter boxes; a boxes containing zero are rejected.
Exact centre margins are reduced by a rational perturbation bound covering the
whole a box. Nonpositive corrected margins mean `:undetermined`, not nonhyperbolicity.

The result carries `scope=:complex_state`. All core transitions are projected to
x-cell pairs, deduplicated, and checked by exact rational rectangle extrema of
`M(x)'Q_jM(x)-Q_k`. The determinant is a separable quadratic at the fixed complex
centre of a; the perturbation estimate controls all other a values in the box.
Only a uniform positive verified margin permits `:proved`; samples only search
for forms. Returned forms, x cells and transitions are inspectable witnesses,
not trusted tokens. See `certify_real_cone_field` for a real-state-only result.

`initial_forms` is an optional SEARCH HINT only, never a certificate: a function
from an x-cell rectangle `(u0,u1,v0,v1)` to a finite 4-tuple form. It cannot make
the exact verification accept an invalid family, and a missing or invalid hint
only changes which forms the search explores.
"""
function certify_cone_field(p; radius=nothing,dims=(48,8),iterations::Integer=4000,
                            samples::Integer=3,max_vertices::Integer=400_000,
                            max_edges::Integer=20_000_000,initial_forms=nothing)
    result = (; status=:failed,reason="",method=:cone_field,scope=:complex_state,
              parameters=nothing,radius=0.0,dims=(0,0),state_dims=(0,0,0,0),core=0,
              cells=0,edges=0,constraints=0,sampled_margin=-Inf,
              margin=_ConeRational(-1),iterations=0,forms=nothing,
              x_cells=nothing,transitions=nothing,parameter_center=nothing,
              parameter_deviation=nothing)
    report(status,reason;extra...) = merge(result,(;status,reason,extra...))
    try
        1 <= iterations <= typemax(Int) && 1 <= samples <= typemax(Int) ||
            throw(ArgumentError("iterations and samples must be positive bounded integers"))
        dims isa Tuple && length(dims)==2 &&
            all(d -> d isa Integer && 0 < d <= typemax(Int),dims) ||
            throw(ArgumentError("cone dims must be two positive bounded integers"))
        max_vertices >= 0 && max_edges >= 0 || throw(ArgumentError("budgets must be nonnegative"))
        data = _henon_data(p)
        r = _henon_radius(data,radius)
        a,deviation = _cone_parameter_enclosure(data.parameters)
        d = map(Int,dims)
        state_dims = (d[1],d[1],d[2],d[2])
        prod(big.(state_dims)) <= max_vertices || throw(ArgumentError("complex cone grid exceeds max_vertices"))
        # The search allocation is bounded independently of graph edge budgets.
        big(samples+big(1))^2 * big(d[1])^2 <= max_vertices*big(64) ||
            throw(ArgumentError("cone sample table exceeds its allocation budget"))
        G = GAIO.BoxGrid(GAIO.Box(ntuple(_->0.0,4),ntuple(_->r,4)),state_dims)
        g = outer_graph(z->henon(z,data.parameters),GAIO.cover(G,:);max_vertices,max_edges)
        core = graph_core(g.adjacency)
        isempty(core) && throw(ArgumentError("empty global core contradicts fixed-point coverage"))
        alive = Set(core)
        xkey(key) = (key[1],key[2])
        xcells = sort!(unique([xkey(g.keys[v]) for v in core]))
        index = Dict(key=>i for (i,key) in enumerate(xcells))
        pairs = Set{Tuple{Int,Int}}()
        nedge = 0
        for v in core, w in g.adjacency[v]
            w in alive || continue
            push!(pairs,(index[xkey(g.keys[v])],index[xkey(g.keys[w])]))
            nedge += 1
        end
        transitions = sort!(collect(pairs))
        isempty(transitions) && throw(ArgumentError("global core has no transitions"))
        geometry = _grid_geometry(G)
        boxes = map(xcells) do key
            u0 = geometry.lower[1]+(key[1]-1)*geometry.step[1]
            v0 = geometry.lower[2]+(key[2]-1)*geometry.step[2]
            (u0,u0+geometry.step[1],v0,v0+geometry.step[2])
        end
        # The search integrates Float64 forms; exact rational hints are demoted
        # here so a rational continuation solution cannot silently push the whole
        # inner loop onto BigInt arithmetic.
        hint = if isnothing(initial_forms)
            nothing
        elseif initial_forms isa Function
            map(boxes) do box
                form = initial_forms(box)
                form isa Tuple && length(form) == 4 && all(x -> x isa Real,form) ||
                    throw(ArgumentError("initial_forms must return a finite 4-tuple of reals"))
                map(Float64,form)
            end
        else
            throw(ArgumentError("initial_forms must be a function of the x-cell rectangle"))
        end
        found = _cone_search_complex(transitions,boxes,a;
                                     iterations=Int(iterations),samples=Int(samples),deviation,
                                     initial_forms=hint)
        info = (;parameters=data.parameters,radius=r,dims=d,state_dims,
                 core=length(core),cells=length(xcells),edges=nedge,
                 constraints=length(transitions),sampled_margin=found.sampled,
                 margin=found.margin,iterations=found.iterations,
                 forms=found.forms,x_cells=xcells,transitions,
                 parameter_center=a,parameter_deviation=deviation)
        found.margin > 0 && return report(:proved,
            "exact Hermitian margins are positive on every complex-state core transition";info...)
        return report(:undetermined,
            "no positive exact complex-state margin within the search budget";info...)
    catch e
        e isa Union{ArgumentError,DimensionMismatch,BoundsError,DomainError,OverflowError,InexactError} || rethrow()
        return report(:failed,sprint(showerror,e))
    end
end
