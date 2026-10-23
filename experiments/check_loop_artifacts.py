"""Independent check of the saved symmetric-loop tables; run from the repository root.

Checks artifact consistency only, not the enclosure computation itself.
"""
import csv
import tomllib
from fractions import Fraction
from pathlib import Path

ROOT = Path('results')
T = {'a-19_40_c-7_4': Fraction(4), 'a-1_c-7_2': Fraction(29, 4), 'a-3_4_c-2': Fraction(6), 'a51_80_c-7_2': Fraction(17, 4)}
FORM_HEADER = ['cell1', 'cell2', 'cell3', 'cell4', 'P', 'gamma', 'delta', 'R']
table = lambda path: list(csv.DictReader(open(path, encoding='utf-8'), delimiter='\t'))
for name, top in T.items():
    d = ROOT / name
    rows = table(d / 'parameter-certificates.tsv')
    lo = [Fraction(r['imag_c_lo']) for r in rows]; hi = [Fraction(r['imag_c_hi']) for r in rows]
    assert lo[0] == 0 and hi[-1] == top and all(hi[i] == lo[i + 1] for i in range(len(rows) - 1))
    m = min(Fraction(r['exact_margin']) for r in rows)
    assert m > 0
    for r in rows:
        forms = table(d / r['witness'])
        assert list(forms[0]) == FORM_HEADER
        cells = {tuple(int(f[k]) for k in FORM_HEADER[:4]) for f in forms}
        assert len(cells) == len(forms) == int(r['vertices'])
        n = 2 ** int(r['level'])
        assert all(1 <= k <= n for c in cells for k in c)
        for f in forms:
            [Fraction(f[k]) for k in FORM_HEADER[4:]]
        assert Fraction(r['radius']) > 0
    words = table(d / 'word-table.tsv')
    L = len(words[0][next(iter(words[0]))])
    assert len(words) == 2 ** L and len({w[next(iter(w))] for w in words}) == 2 ** L
    assert all(int(w['center_boxes']) > 0 and (w['contact0'] == 'true') != (w['contact1'] == 'true') for w in words)
    assert all(w['output'] == ('0' if w['contact0'] == 'true' else '1') for w in words)
    proof = tomllib.load(open(d / 'loop-proof.toml', 'rb'))
    assert proof['status'] == 'proved' and proof['pieces'] == len(rows) and Fraction(proof['minimum_margin']) == m
    assert proof['classification']['words'] == len(words) == 2 ** (proof['classification']['memory'] + proof['classification']['anticipation'] + 1)
    print(f'{name}: {len(rows)} contiguous pieces on [0,{top}], min exact margin {float(m):.6g} > 0, forms cover every vertex, {len(words)} words all exclusive')
