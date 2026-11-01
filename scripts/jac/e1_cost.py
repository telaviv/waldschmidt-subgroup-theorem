"""Stage A1: a kernel-cost model for the E1 range declarations, and adaptive X-slot ranges (UNTRUSTED helper).

cost(range) = sum over X-row pairs (ra, rb) of a term whose NF row meets the range of
              (#Y-products of the pair) * A  +  |NF row ∩ range| * (#Y-products ... not needed) ...
We use: cost = Σ_{pairs meeting range} ny(pair) + U * Σ_pairs |row ∩ range|, ny = |ra.2|·|rb.2|.
Calibrated against measured peaks (STAGE_A1 §10).  Usage: from e1_cost import ranges_for
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import slots
from e1_data import FAMILIES, DA, Wn, W4n, dig
ROOT = os.path.join(HERE, '..', '..', 'LSG', 'Jac')
FAM_DA = {'E40': 'X0W4', 'E44': 'X0W4', 'E04': 'X0W', 'F4X': 'X4W4', 'F4Y': 'Y4W4'}
U = 1.0

def load_rows(path, pat):
    src = open(os.path.join(ROOT, 'Data', path), encoding='utf-8').read()
    rows = {}
    for m in re.finditer(pat, src):
        rows[int(m.group(1))] = [int(a) for a, _, _ in re.findall(r'\((\d+), (\d+), (true|false)\)', m.group(2))]
    return rows

_cache = {}
def tables():
    if not _cache:
        _cache['5'] = load_rows('Table5.lean', r'noncomputable def l5_\d+ : Leaf := ⟨(\d+), \d+, \[(.*?)\],\n')
        _cache['4'] = load_rows('Table.lean', r'noncomputable def lf\d+ : Leaf := ⟨(\d+), \d+, \[(.*?)\],')
        _cache['laws'] = slots.load_laws()
    return _cache

def sp_rows_law(laws, k, m):
    return [(a, len(r)) for a, r in laws[(k, m)]]

def sp_rows_poly(poly):
    rows = {}
    for (a, b), v in poly.items():
        rows[a] = rows.get(a, 0) + 1
    return sorted(rows.items())

def shift_rows(rows, f, side):
    if side == 'X':
        return [(a + 8 ** f, n) for a, n in rows]
    return rows

def pairs_of(fam, j, l):
    """List of (X-code sum, ny) over all X-row pairs of all terms of identity (fam, j, l)."""
    t = tables()
    laws = t['laws']
    m, side, Win, sin, c, Wout, sout, f = FAMILIES[fam]
    da = FAM_DA[fam]
    DAs = {}
    def dap(ll):
        if ll not in DAs:
            DAs[ll] = sp_rows_poly(DA(laws, ll, m, side, Win, j))
        return DAs[ll]
    terms = [(sp_rows_law(laws, c, m), dap(l)), (sp_rows_law(laws, l, m), dap(c))]
    for cd, coef in sorted(Wout.get((j, l), {}).items()):
        ab = [i for i in range(9) for _ in range(dig(cd, i))]
        terms.append((shift_rows(sp_rows_law(laws, ab[0], m), f, side), sp_rows_law(laws, ab[1], m)))
    out = []
    for A, B in terms:
        for a, na in A:
            for b, nb in B:
                out.append((a + b, na * nb))
    return out

def cost_profile(fam, j, l):
    t = tables()
    side = FAMILIES[fam][1]
    rows = t['5'] if side == 'X' else t['4']
    prs = pairs_of(fam, j, l)
    return [(rows[key], ny) for key, ny in prs]

def range_cost(prof, lo, hi):
    tot = 0.0
    for row, ny in prof:
        k = sum(1 for s in row if lo <= s < hi)
        if k:
            tot += ny + U * k
    return tot

def ranges_for(fam, j, l, budget):
    side = FAMILIES[fam][1]
    nslot = 225 if side == 'X' else 144
    prof = cost_profile(fam, j, l)
    rs, lo = [], 0
    while lo < nslot:
        hi = lo + 1
        while hi < nslot and range_cost(prof, lo, hi + 1) <= budget:
            hi += 1
        rs.append((lo, hi))
        lo = hi
    return rs, [range_cost(prof, a, b) for a, b in rs]

if __name__ == '__main__':
    prof = cost_profile('F4X', 0, 0)
    for lo, hi in [(0, 25), (25, 50), (50, 75), (75, 100), (100, 125), (125, 150), (150, 175), (175, 200), (200, 225),
                   (175, 187), (187, 200), (175, 181)]:
        print(lo, hi, range_cost(prof, lo, hi))
