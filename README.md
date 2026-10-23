# OnLoops.jl

Computer-assisted proof of the monodromy actions of four conjugate-symmetric
loops of the complex Hénon map

$$H_{a,c}(x, y) = (x^2 + c - a y,\ x),$$

used for Proposition 5.2 and Appendix B of [[3]](#references).

OnLoops.jl is a Julia re-implementation of the computational methods of
Zin Arai's paper [[1]](#references), written with reference to the author's
supplemental programs and data [[2]](#references), and published with his
permission. It does not include or redistribute those materials; obtain them
from [[2]](#references).

## Results

Each loop has a fixed real $a$. Its $c$-component passes, at the times
$t = j/6$ ($j = 0, \dots, 6$), through

$$c_0 \to c_0 + iT \to c_t + iT \to c_t \to c_t - iT \to c_0 - iT \to c_0,$$

so $\gamma(1-t) = \overline{\gamma(t)}$ and the loop passes through the
*midpoint* $(a, c_t)$ at $t = 1/2$. The basepoint $(a, c_0)$ is real.
In [3] the loop is $\gamma_P$, $a = a_P$ and $c_t = c_P$, where $P$ is the
numbered parameter region.

| Region $P$ in [3] | Name (`results/<name>/`) | Midpoint $(a, c_t)$ | $c_0$ | $T$ | Pieces | Minimum exact margin | Window $[-m, n]$ | Minimal window | Flipped words |
| ---: | --- | --- | ---: | ---: | ---: | --- | --- | --- | ---: |
| 2 | `a51_80_c-7_2` | $(51/80, -7/2)$ | $-7$ | $17/4$ | 124 | $> 0.0512$ | $[-2, 3]$ (64 words) | $[-2, 3]$ | 2 |
| 4 | `a-3_4_c-2` | $(-3/4, -2)$ | $-8$ | $6$ | 152 | $> 0.00918$ | $[-2, 3]$ (64 words) | $[-2, 3]$ | 10 |
| 5 | `a-19_40_c-7_4` | $(-19/40, -7/4)$ | $-6$ | $4$ | 120 | $> 0.0197$ | $[-2, 4]$ (128 words) | $[-2, 4]$ | 18 |
| 7 | `a-1_c-7_2` | $(-1, -7/2)$ | $-10$ | $29/4$ | 172 | $> 0.00228$ | $[-3, 4]$ (256 words) | $[-3, 3]$ | 32 |

The computed action $\rho = h_1 \circ h_0^{-1}$ is given by `word-table.tsv`:
for every word $s_{-m} \cdots s_n$ of the window, the symbol $\rho(s)_0$.
Symbol $0$ means $\mathop{\mathrm{Re}} y > 0$ and symbol $1$ means
$\mathop{\mathrm{Re}} y < 0$. "Flipped words" are the words with
$\rho(s)_0 \ne s_0$; they are listed in `loop-proof.toml`. In all four cases
the action is an involution, as checked on every context of twice the window.
The minimal window is the shortest sub-window on which the table is still a
function of the word (minimality as a block rule). The flipped words of each
table are exactly the words in which $s_0$ is the starred symbol of one of the
markers listed for its region in Table 1 of [3].

## What the computer checks and what the paper proves

| Claimed by the computation (this repository) | Proved or cited in [3], Appendix B |
| --- | --- |
| Exact rational checks of the loop (S0) and of the partition of the right edge (S1). | (i) The cone condition implies uniform hyperbolicity on the chain recurrent set $R(H_p)$ ([3], B.2; [1], Theorem 9 and Lemma 11). |
| On every closed piece of the right edge, a closed-box enclosure of $K_p$ whose edges all satisfy the cone condition with a positive exact margin (S2, S3). | (ii) $\mathop{\mathrm{Re}} y \ne 0$ on $K_{a,c}$ in HOV with $\mathop{\mathrm{Re}} c \le 0$, so the coding by the sign of $\mathop{\mathrm{Re}} y$ continues there ([3], Lemma B.1). |
| Transport of the two labels through the space-time enclosure (S5). | (iii) $R$-structural stability and $K_p = R(H_p)$, giving the horseshoe along the loop (S4; [3], B.2; [1], Corollary 6). |
| At the midpoint, every word touches exactly one conjugated label (S6), and the resulting rule (S7). | (iv) $\rho(\gamma) = h \circ \kappa \circ h^{-1}$, which reduces the action to the upper half of the loop and the midpoint classification ([3], (B.1); [1], proof of Theorem 3). |

Step S4 is not computed. Every proof condition in the code is checked with
`require`, which throws `ArgumentError`; nothing relies on `@assert`.

## Proof steps

The entry point is [experiments/certify_symmetric_loops.jl](experiments/certify_symmetric_loops.jl).
`prove_symmetric_loop` runs the steps below in order; each step lives in
[experiments/loop_proof/](experiments/loop_proof/).

| Step | Statement | Code |
| --- | --- | --- |
| S0 | The loop is exactly closed; the basepoint is real and in the DN region ($D = -4c_0/(1+\lvert a\rvert)^2 - 5 > 0$, $D^2 > 20$); $\lvert a\rvert \le 1$; $c_0 < c_t < 0$; the left and top edges lie in the HOV region ($c_0^2 > \theta^2$, $c_t^2 + T^2 > \theta^2$, $\theta = 2(1+\lvert a\rvert)^2$); $\gamma(1-t) = \overline{\gamma(t)}$. | `LOOP_SPECS`, `symmetric_loop` (`loop.jl`); `RationalLoop` (`src/OnLoops.jl`); `_loop_geometry_check` (`src/monodromy.jl`) |
| S1 | The pieces in `parts.tsv` cover $[0, T]$ of the right edge $c = c_t + iu$ without gaps. | `read_pieces`, `require_contiguous` (`loop.jl`) |
| S2 | For every parameter $p$ of a piece, every bounded orbit lies in the boxes of a closed-box graph and follows its edges. The graph is rebuilt from the whole region $[-r, r]^4$ ($r$ from [1], Lemma 11) at each run. | `global_cover`, `shrink_cover`, `shrink_edge` (`cover.jl`); `outer_graph`, `graph_core` (`src/sets_graphs.jl`); `henon_radius` (`src/henon_data.jl`) |
| S3 | For Hermitian forms $Q_k$ on the cells and every edge $(k, j)$: $M(x,a)^* Q_j M(x,a) - Q_k \succeq \varepsilon I$ with $\varepsilon > 0$, where $M(x, a) = \begin{pmatrix} 2x & -a \\ 1 & 0 \end{pmatrix}$, computed in exact rational arithmetic. | `exact_cone_margin` (`cone_forms.jl`); `_cone_parameter_margin` (`src/cone_field.jl`) |
| S5 | The labels $\mathop{\mathrm{Re}} y > 0$ and $\mathop{\mathrm{Re}} y < 0$ at $u = T$ are carried down to $u = 0$ through the connected components of the closed-box contact graph of all pieces. | `transport_box_partitions` (`transport.jl`) |
| S6 | At the midpoint (level 8), a word is assigned output $b$ only if the enclosure of its cylinder does not touch the conjugate of the enclosure of label $1-b$ (opposite-label exclusion). Windows are tried from the smallest; the first fully determined one is used. | `classify_midpoint_rule` (`classify.jl`); `_cylinder_indices` (`src/monodromy.jl`) |
| S7 | Every word touches exactly one label; involution check; minimal windows. | `rule_from_table`, `involution_check`, `minimal_windows` (`rule.jl`) |

The stored forms are search hints, not proof tokens: `prove` rebuilds every
enclosure and recomputes the exact margin of the stored forms on all of its
edges. The numerical search for forms (`search_cone_forms`) and for pieces
(`search`, `collect`) is not part of the proof.

## Repository layout

| Path | Contents |
| --- | --- |
| `src/` | The `OnLoops` package: Hénon map, closed-box graphs, enclosure radius, exact cone margins, loop checks. |
| `experiments/certify_symmetric_loops.jl` | Entry point for the four loops (`prove`, and the non-proof `search`, `collect`, `piece`). |
| `experiments/loop_proof/` | Proof steps S0–S7. |
| `experiments/check_loop_artifacts.py` | Independent consistency check of the saved tables in Python, without Julia. |
| `results/<name>/` | Input partition, forms, certificates, word table and proof summary of each loop. |
| `test/` | Regression tests (`runtests.jl` for the package, `loop_proof.jl` for the proof steps). |

## Saved results

All files are UTF-8 text. Rational numbers are exact `p/q` (integers too, e.g. `5/1`).

| File | Contents |
| --- | --- |
| `parts.tsv` | Input: the partition of the right edge $c = c_t + iu$. Columns `imag_c_lo imag_c_hi level`; the grid has $2^{\text{level}}$ cells per state axis. |
| `piece-*-forms.tsv` | Cone forms of one piece, one row per state cell: `cell1 cell2 cell3 cell4 P gamma delta R`. Cell $k$ is $[-r+(k-1)h, -r+kh]$ on each axis with $h = 2r/2^{\text{level}}$; the form is $\begin{pmatrix} P & \gamma + i\delta \\ \gamma - i\delta & R \end{pmatrix}$. |
| `parameter-certificates.tsv` | Per piece: level, state radius $r$, numbers of vertices and edges, exact margin `exact_margin`, and the forms file `witness`. |
| `word-table.tsv` | Every word of the window: number of center boxes, contact with each label, output. |
| `loop-proof.toml` | Summary: loop corners, number of pieces, minimum margin, transport statistics, window, involution, minimal windows, flipped words, and the run environment with the SHA-256 of the entry point, `experiments/loop_proof/`, `src/` and `Manifest.toml`. |

## Running

Requirements: Julia 1.12 or later (the results were produced with Julia 1.13.0
on Windows; `Manifest.toml` pins every dependency, including GAIO.jl at a
fixed Git revision). Run every command from the repository root.

```sh
julia --project=. -e 'using Pkg; Pkg.instantiate()'
julia --project=. --threads=1 test/runtests.jl
julia --project=. --threads=1 test/loop_proof.jl
```

Re-run the proof of one loop:

```sh
julia --project=. --threads=1 experiments/certify_symmetric_loops.jl prove a-1_c-7_2
```

`prove` reads `parts.tsv` and the forms, rebuilds all enclosures, and
rewrites `word-table.tsv`, `parameter-certificates.tsv` and `loop-proof.toml`
in `results/<name>/`. It exits with a nonzero code unless every step succeeds.
One run took between about 4 and 16 minutes on one thread. Only the
`[environment]` section of `loop-proof.toml` (run time, Julia version and
source hashes) is expected to change.

Check the saved tables without Julia (Python 3.11 or later):

```sh
python experiments/check_loop_artifacts.py
```

This checks that the pieces cover $[0, T]$, that every exact margin is
positive, that each forms file has one row per vertex, that every word touches
exactly one label, and that `loop-proof.toml` agrees with the tables. It does
not check the enclosures themselves.

## References

1. Zin Arai, "On loops in the hyperbolic locus of the complex Hénon map and
   their monodromies", *Physica D: Nonlinear Phenomena* **334** (2016), 133–140.
   [doi:10.1016/j.physd.2016.02.006](https://doi.org/10.1016/j.physd.2016.02.006)
2. Zin Arai, supplemental materials (data, programs) for [1]:
   <https://github.com/zin-arai/zin-arai.github.io/tree/main/loops>
3. Toshiki Usui, "Structure of decomposition by 2-cascades for SFTs and its
   application to real Hénon maps", in preparation.

## License

The OnLoops.jl code and the files in `results/` are released under the
[MIT License](LICENSE). This license does not apply to the materials of [2],
which are not included here.
