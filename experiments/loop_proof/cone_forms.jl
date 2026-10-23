# Step S3: hyperbolicity of K_p by a cone field.
#
# Every cell k of the enclosure gets a Hermitian form Q_k = [P  g+id; g-id  R].
# The proof is `exact_cone_margin(cover, forms) > 0`: an exact rational lower
# bound of the smallest eigenvalue of M(x,a)^* Q_j M(x,a) - Q_k over every edge
# (k, j), every x in that edge's x box and every a in the parameter box, where
# M(x,a) = [2x  -a; 1  0] is the derivative of H. `search_cone_forms` only
# proposes forms; it is not part of the proof.

const CONE_FORM_HEADER = "cell1\tcell2\tcell3\tcell4\tP\tgamma\tdelta\tR"

"""
    exact_cone_margin(cover, forms)

Minimum over all edges of the exact margin computed by
`OnLoops._cone_parameter_margin` (src/cone_field.jl), in `Rational{BigInt}`.
Positive means the cone condition holds on the whole enclosure.
"""
function exact_cone_margin(cover, forms)
    return minimum(enumerate(cover.edges)) do (e, (k, j))
        OnLoops._cone_parameter_margin(forms[k], forms[j], cover.parameter_center,
                                       cover.parameter_deviation, cover.edge_x_boxes[e])
    end
end

"""
    write_cone_forms(path, cells, forms)

Save one form per cell as exact `p/q` text, one row per cell.
"""
function write_cone_forms(path, cells, forms)
    length(cells) == length(forms) || throw(DimensionMismatch("one form per cell"))
    open(path, "w") do io
        println(io, CONE_FORM_HEADER)
        for (cell, form) in zip(cells, forms)
            println(io, join(Tuple(cell), '\t'), '\t', join(map(rational_text, form), '\t'))
        end
    end
end

"""
    read_cone_forms(path, cells)

Forms stored by `write_cone_forms`, in the order of `cells`, or `nothing` when
the file is missing or lacks one of the cells. Malformed files throw. The
result is only a candidate: callers must recheck it with `exact_cone_margin`
on a freshly built enclosure.
"""
function read_cone_forms(path, cells)
    isfile(path) || return nothing
    lines = readlines(path)
    !isempty(lines) && first(lines) == CONE_FORM_HEADER || throw(ArgumentError("$path is not a cone form table"))
    rows = split.(lines[2:end], '\t')
    all(row -> length(row) == 8, rows) || throw(ArgumentError("$path rows must have 8 columns"))
    form_of = Dict(ntuple(j -> parse(Int, row[j]), 4) => ntuple(j -> parse(Q, row[4+j]), 4) for row in rows)
    length(form_of) == length(rows) || throw(ArgumentError("$path repeats a cell"))
    all(cell -> haskey(form_of, Tuple(cell)), cells) || return nothing
    return [form_of[Tuple(cell)] for cell in cells]
end

"""
    search_cone_forms(cover; sweeps=500, samples=3)

Non-rigorous Float64 search for forms. Starts from `Q = diag(1, -|a|)` on every
cell and, for each edge, moves the two forms along the eigenvector of the
smallest sampled eigenvalue (a projected subgradient step). Every 25 sweeps it
rounds the forms to rationals and returns them if `exact_cone_margin` is
positive. Returns `nothing` when the budget runs out.
"""
function search_cone_forms(cover; sweeps=500, samples=3)
    a = ComplexF64(cover.parameter_center)
    sample_points = map(cover.edge_x_boxes) do b
        unique([complex(Float64(b[1] + (b[2] - b[1])*i/samples), Float64(b[3] + (b[4] - b[3])*j/samples))
                for i in 0:samples for j in 0:samples])
    end
    forms = fill((1.0, 0.0, 0.0, -abs(a)), length(cover.cells))
    smallest_eigen(k, j, x) = OnLoops._cone_complex_eigen(OnLoops._cone_complex_matrix(forms[k], forms[j], x, a)...)
    for sweep in 1:sweeps
        for (e, (k, j)) in enumerate(cover.edges)
            worst, wu, wv, wx = Inf, 0.0 + 0im, 0.0 + 0im, 0.0 + 0im
            for x in sample_points[e]
                lambda, u, v = smallest_eigen(k, j, x)
                lambda < worst && ((worst, wu, wv, wx) = (lambda, u, v, x))
            end
            worst < 1 || continue
            image_u, image_v = 2wx*wu - a*wv, wu
            denominator = 1 + (abs2(image_u) + abs2(image_v))^2
            k == j && (denominator -= 2abs2(conj(wu)*image_u + conj(wv)*image_v))
            denominator > 1e-20 || continue
            step = (1 - worst)/denominator
            forms[k] = OnLoops._cone_update(forms[k], wu, wv, -step)
            forms[j] = OnLoops._cone_update(forms[j], image_u, image_v, step)
        end
        (sweep % 25 == 0 || sweep == sweeps) || continue
        sampled = minimum(first(smallest_eigen(k, j, x)) for (e, (k, j)) in enumerate(cover.edges) for x in sample_points[e])
        margin = nothing
        if sampled > 0 || sweep == sweeps
            exact = [map(Q, form) for form in forms]
            margin = exact_cone_margin(cover, exact)
            if margin > 0
                println((sweep=sweep, sampled=sampled, exact_margin=Float64(margin)))
                return exact
            end
        end
        println((sweep=sweep, sampled=sampled, exact_margin=isnothing(margin) ? nothing : Float64(margin)))
        flush(stdout)
        isfinite(sampled) || return nothing
    end
    println("UNDETERMINED: no exact positive certificate within the sweep budget.")
    return nothing
end
