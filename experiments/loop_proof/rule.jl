# Step S7: the determined word table as a block rule rho(s)_0 = f(s_{-m}, ..., s_n).

"""
    rule_from_table(table)

`Dict(word => output bit)` of a fully determined table from `classify_midpoint_rule`.
"""
function rule_from_table(table)
    require(all(row -> row.output in (:label0, :label1), table), "every word must be determined")
    return Dict(Tuple(row.word) => (row.output == :label0 ? 0 : 1) for row in table)
end

"""
    apply_rule(rule, m, n, s, i)

`rho(s)_i = rule(s_{i-m}, ..., s_{i+n})` for a sequence given as a function `s(j)`.
"""
apply_rule(rule, m, n, s, i) = rule[ntuple(k -> s(i - m + k - 1), m + n + 1)]

"""
    involution_check(rule, m, n)

True when `rho(rho(s))_0 = s_0` for every sequence. `rho(rho(s))_0` depends on
`s_{-2m}, ..., s_{2n}`, so all `2^(2m+2n+1)` such contexts are enumerated.
"""
function involution_check(rule, m, n)
    L = 2m + 2n + 1
    for bits in 0:2^L-1
        s(j) = (bits >> (L - 1 - (j + m + n))) & 1
        image(i) = apply_rule(rule, m, n, s, i)
        apply_rule(rule, m, n, image, 0) == s(0) || return false
    end
    return true
end

"""
    minimal_windows(rule, m, n)

The shortest subwindows `[i, j]` of `[-m, n]` such that the output depends only
on `s_i, ..., s_j`, i.e. no two words that agree on `[i, j]` have different outputs.
"""
function minimal_windows(rule, m, n)
    factors(i, j) = begin
        output_of = Dict{Any,Int}()
        all(get!(output_of, word[(i+m+1):(j+m+1)], bit) == bit for (word, bit) in rule)
    end
    windows = [(i, i + len - 1) for len in 1:m+n+1 for i in -m:n if i + len - 1 <= n]
    found = filter(w -> factors(w...), windows)
    shortest = minimum(w -> w[2] - w[1], found)
    return filter(w -> w[2] - w[1] == shortest, found)
end
