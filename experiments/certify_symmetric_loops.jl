# Proof of the monodromy action of the conjugate-symmetric loops in LOOP_SPECS.
# The steps S0-S7 are described in README.md ("Proof steps").
#
#   julia --project=. --threads=1 experiments/certify_symmetric_loops.jl prove <name>
#   ... search <name> <stride> <offset>   choose pieces (not part of the proof)
#   ... collect <name>                    write parts.tsv from the search logs
#   ... piece <name> <lo> <hi> <level>    certify one piece
using SHA
using TOML

include("loop_proof/common.jl")
include("loop_proof/loop.jl")          # S0, S1
include("loop_proof/cover.jl")         # S2
include("loop_proof/cone_forms.jl")    # S3
include("loop_proof/transport.jl")     # S5
include("loop_proof/classify.jl")      # S6
include("loop_proof/rule.jl")          # S7

const WINDOWS = ((1, 2), (2, 2), (2, 3), (2, 4), (3, 4), (3, 5), (4, 5), (4, 6))
const PRISM_BUDGET = 4_000_000

"""
    certify_piece(spec, dir, piece; sweeps=500, search=true)

Steps S2 and S3 for one piece. Builds the enclosure from scratch, reads the
stored forms `<piece>-forms.tsv` and accepts the piece only if their exact
margin on this new enclosure is positive. Without valid stored forms it runs
the search (if `search`), saves its forms, reads them back and checks them the
same way. Returns a receipt with `proved`, the margin and the state boxes.
"""
function certify_piece(spec, dir, piece; sweeps=500, search=true)
    lo, hi, level = piece
    require(0 <= lo < hi <= spec.T && level in 6:8, "invalid piece $piece")
    p = piece_parameters(spec, lo, hi)
    forms_file = joinpath(dir, piece_tag(lo, hi, level) * "-forms.tsv")
    cover = shrink_cover(global_cover(p; max_level=level); passes=15)
    require(exact_endpoints(cover.parameters) == exact_endpoints(p), "the enclosure was built for another parameter box")
    forms = read_cone_forms(forms_file, cover.cells)
    if isnothing(forms) || exact_cone_margin(cover, forms) <= 0
        failed = (proved=false, range=(lo, hi), level=level)
        search || return failed
        found = search_cone_forms(cover; sweeps)
        isnothing(found) && return failed
        write_cone_forms(forms_file, cover.cells, found)
        forms = read_cone_forms(forms_file, cover.cells)
    end
    margin = exact_cone_margin(cover, forms)
    require(margin > 0, "stored forms do not give a positive exact margin")
    return (proved=true, range=(lo, hi), level=level, radius=Q(cover.radius), margin=margin,
            margin_float=Float64(margin), vertices=length(cover.cells), edges=length(cover.edges),
            boxes=cover.boxes, witness=forms_file)
end

"""
    certify_all_pieces(spec, dir, pieces)

S2 and S3 on every piece. Returns the receipts and the state boxes of each
piece (the layers for S5), or `nothing` at the first piece without a proof.
"""
function certify_all_pieces(spec, dir, pieces)
    layers = Vector{Vector{StateBox}}()
    receipts = []
    for (i, piece) in enumerate(pieces)
        receipt = certify_piece(spec, dir, piece)
        if !receipt.proved
            println((status=:undetermined, reason=:no_exact_cone_witness, parameter_interval=receipt.range))
            return nothing
        end
        push!(layers, receipt.boxes)
        push!(receipts, merge(receipt, (boxes=nothing,)))
        require(sum(big(length(B)) for B in layers) <= PRISM_BUDGET, "prism vertex budget exceeded")
        println((certified=i, of=length(pieces), imag_c_interval=receipt.range, margin=receipt.margin_float,
                 vertices=receipt.vertices, edges=receipt.edges))
        flush(stdout)
    end
    return receipts, layers
end

"""
    midpoint_labels(layers)

S5. Transports the sign of `Re y` from `u = T` (last piece) down to `u = 0`
and returns the transport statistics with the label enclosures `A0`, `A1`
at the midpoint.
"""
function midpoint_labels(layers)
    from_top = reverse(layers)
    transport = transport_box_partitions(from_top; max_vertices=PRISM_BUDGET)
    println((transport..., terminal_masks=nothing))
    flush(stdout)
    midpoint_boxes = last(from_top)
    A0 = [B for (B, mask) in zip(midpoint_boxes, transport.terminal_masks) if has_label0(mask)]
    A1 = [B for (B, mask) in zip(midpoint_boxes, transport.terminal_masks) if has_label1(mask)]
    return transport, A0, A1
end

"""
    classify_first_window(loop, A0, A1)

S6. Builds the enclosure at the exact midpoint parameter (level 8) and tries
the windows in `WINDOWS` from the smallest; returns the first fully
determined classification, or the last result if none is.
"""
function classify_first_window(loop, A0, A1)
    p = map(input_interval, loop.points[4])
    midpoint = shrink_cover(global_cover(p; max_level=8); passes=15)
    require(exact_endpoints(midpoint.parameters) == exact_endpoints(p), "the midpoint enclosure has the wrong parameter")
    result = nothing
    for (m, n) in WINDOWS
        result = classify_midpoint_rule(midpoint.boxes, midpoint.edges, A0, A1;
                                        memory=m, anticipation=n, max_words=2^12)
        println((memory=m, anticipation=n, status=result.status,
                 undetermined=count(r -> r.output == :undetermined, result.table),
                 inconsistent=count(r -> r.output == :inconsistent, result.table)))
        flush(stdout)
        result.status in (:determined, :failed) && break
    end
    return result
end

function write_word_table(path, result)
    open(path, "w") do io
        println(io, "word_minus$(result.memory)_to_plus$(result.anticipation)\tcenter_boxes\tcontact0\tcontact1\toutput")
        for row in result.table
            println(io, join(row.word), "\t", row.boxes, "\t", row.contact0, "\t", row.contact1, "\t",
                    row.output == :label0 ? 0 : 1)
        end
    end
end

function write_parameter_certificates(path, receipts)
    open(path, "w") do io
        println(io, "imag_c_lo\timag_c_hi\tlevel\tradius\tvertices\tedges\texact_margin\twitness")
        for r in receipts
            println(io, rational_text(r.range[1]), "\t", rational_text(r.range[2]), "\t", r.level, "\t",
                    rational_text(r.radius), "\t", r.vertices, "\t", r.edges, "\t", rational_text(r.margin), "\t",
                    basename(r.witness))
        end
    end
end

"""
    source_hashes(root)

SHA-256 of every file the proof runs: this entry, `experiments/loop_proof/`,
`src/` and `Manifest.toml`, keyed by path relative to `root`.
"""
function source_hashes(root)
    files = [joinpath(root, "experiments", "certify_symmetric_loops.jl"), joinpath(root, "Manifest.toml")]
    for dir in (joinpath(root, "experiments", "loop_proof"), joinpath(root, "src"))
        append!(files, filter(f -> endswith(f, ".jl"), readdir(dir; join=true)))
    end
    return Dict(replace(relpath(f, root), '\\' => '/') => bytes2hex(sha256(read(f))) for f in files)
end

"""
    prove_symmetric_loop(name)

Run S0-S7 for `LOOP_SPECS[name]` and write `word-table.tsv`,
`parameter-certificates.tsv` and `loop-proof.toml` to `spec_dir(name)`.
"""
function prove_symmetric_loop(name)
    spec, dir = LOOP_SPECS[name], spec_dir(name)
    root = normpath(joinpath(@__DIR__, ".."))
    require(realpath(pwd()) == realpath(root), "run from the repository root")
    started = time()

    loop = symmetric_loop(spec)                                   # S0
    pieces = read_pieces(dir)                                     # S1
    require_contiguous(pieces, spec.T)
    certified = certify_all_pieces(spec, dir, pieces)            # S2, S3
    isnothing(certified) && return (status=:undetermined,)
    receipts, layers = certified
    transport, A0, A1 = midpoint_labels(layers)                   # S5
    result = classify_first_window(loop, A0, A1)                  # S6
    result.status == :determined || return (status=result.status,)

    m, n = result.memory, result.anticipation                     # S7
    rule = rule_from_table(result.table)
    require(length(rule) == 2^(m + n + 1), "the table must list every word once")
    require(all(r -> r.boxes > 0 && xor(r.contact0, r.contact1), result.table),
            "every word must touch exactly one conjugated label")
    involution = involution_check(rule, m, n)
    windows_found = minimal_windows(rule, m, n)
    flips = sort([join(word) for (word, bit) in rule if bit != word[m+1]])
    minimum_margin = minimum(r.margin for r in receipts)

    write_word_table(joinpath(dir, "word-table.tsv"), result)
    write_parameter_certificates(joinpath(dir, "parameter-certificates.tsv"), receipts)
    environment = Dict("julia" => string(VERSION), "threads" => Threads.nthreads(),
                       "seconds" => time() - started, "source_sha256" => source_hashes(root))
    summary = Dict(
        "status" => "proved", "name" => name,
        "spec" => Dict(string(k) => rational_text(v) for (k, v) in pairs(spec)),
        "loop" => Dict("times" => rational_text.(loop.times),
                       "points_a_re_a_im_c_re_c_im" => [collect(rational_text.(z)) for z in loop.points]),
        "pieces" => length(receipts), "minimum_margin" => rational_text(minimum_margin),
        "transport" => Dict(string(k) => getfield(transport, k)
                            for k in (:vertices, :components, :collision_components, :terminal_collisions,
                                      :seedless_components, :seedless_boxes, :contact_candidates)),
        "classification" => Dict("memory" => m, "anticipation" => n, "words" => length(result.table),
                                 "retained_vertices" => result.retained_vertices,
                                 "input_overlap" => result.input_overlap,
                                 "input_unlabelled" => result.input_unlabelled,
                                 "output_overlap" => result.output_overlap),
        "involution" => involution, "minimal_windows" => [collect(w) for w in windows_found],
        "flipped_words" => flips, "environment" => environment)
    open(io -> TOML.print(io, summary; sorted=true), joinpath(dir, "loop-proof.toml"), "w")
    println((status=:proved, name, pieces=length(receipts), minimum_margin=Float64(minimum_margin),
             prism_vertices=transport.vertices, components=transport.components,
             collisions=transport.collision_components, seedless_boxes=transport.seedless_boxes,
             memory=m, anticipation=n, involution, minimal_windows=windows_found, flipped_words=length(flips)))
    foreach(println, flips)
    return (status=:proved, summary)
end

"""
    search_pieces(name, stride, offset)

Try the initial pieces whose index `i` has `i % stride == offset`. A failed
piece is retried at level 7, then bisected down to width 1/4096. Results are
appended to `search-<offset>-of-<stride>.tsv`. Only `collect_pieces` and
`prove` turn these into a proof.
"""
function search_pieces(name, stride, offset)
    spec, dir = LOOP_SPECS[name], spec_dir(name)
    mkpath(dir)
    log = joinpath(dir, "search-$(offset)-of-$(stride).tsv")
    pending = reverse([piece for (i, piece) in enumerate(initial_pieces(spec.T)) if i % stride == offset])
    while !isempty(pending)
        lo, hi, level = pop!(pending)
        receipt = certify_piece(spec, dir, (lo, hi, level))
        open(log, "a") do io
            println(io, rational_text(lo), "\t", rational_text(hi), "\t", level, "\t", receipt.proved, "\t",
                    receipt.proved ? receipt.margin_float : "")
        end
        println((piece=(lo, hi, level), proved=receipt.proved, margin=receipt.proved ? receipt.margin_float : nothing))
        flush(stdout)
        receipt.proved && continue
        if level < 7
            push!(pending, (lo, hi, 7))
        elseif hi - lo > Q(1, 4096)
            middle = (lo + hi)/2
            push!(pending, (middle, hi, 7), (lo, middle, 7))
        else
            println((status=:undetermined, piece=(lo, hi, level)))
        end
    end
end

"""
    collect_pieces(name)

Chain the successful search results into `parts.tsv`, starting at `u = 0` and
taking at each point the widest successful piece (lowest level on ties).
"""
function collect_pieces(name)
    spec, dir = LOOP_SPECS[name], spec_dir(name)
    proved = Piece[]
    for file in filter(f -> startswith(f, "search-") && endswith(f, ".tsv"), readdir(dir))
        for row in split.(readlines(joinpath(dir, file)), '\t')
            row[4] == "true" && push!(proved, (parse(Q, row[1]), parse(Q, row[2]), parse(Int, row[3])))
        end
    end
    chain = Piece[]
    u = Q(0)
    while u < spec.T
        starting_here = filter(piece -> piece[1] == u, proved)
        isempty(starting_here) && return (complete=false, gap_at=u)
        best = starting_here[argmin([(lo - hi, level) for (lo, hi, level) in starting_here])]
        push!(chain, best)
        u = best[2]
    end
    write_pieces(dir, chain)
    return (complete=true, pieces=length(chain))
end

if abspath(PROGRAM_FILE) == @__FILE__
    command, name = ARGS[1], ARGS[2]
    if command == "search"
        search_pieces(name, parse(Int, ARGS[3]), parse(Int, ARGS[4]))
    elseif command == "collect"
        println(collect_pieces(name))
    elseif command == "piece"
        mkpath(spec_dir(name))
        piece = (parse(Q, ARGS[3]), parse(Q, ARGS[4]), parse(Int, ARGS[5]))
        receipt = certify_piece(LOOP_SPECS[name], spec_dir(name), piece)
        println((proved=receipt.proved, margin=receipt.proved ? receipt.margin_float : nothing))
    elseif command == "prove"
        result = @time prove_symmetric_loop(name)
        result.status == :proved || exit(2)
    else
        error("unknown command $command")
    end
end
