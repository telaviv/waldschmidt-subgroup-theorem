"""E1 data (merged derivatives) and checker bounds. UNTRUSTED. Imported by gen_jac_e1.py."""
import json, os, sys
from collections import defaultdict
from fractions import Fraction
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import slots
def loadW(fn, scale):
    raw = json.load(open(os.path.join(HERE, fn)))
    W = {}
    for k, v in raw.items():
        j, i = map(int, k.split(','))
        poly = {}
        for (a, b), c in v:
            cc = Fraction(c) * scale
            assert cc.denominator == 1
            poly[8 ** a + 8 ** b] = poly.get(8 ** a + 8 ** b, 0) + int(cc)
        W[(j - 1, i)] = {k2: v2 for k2, v2 in poly.items() if v2}
    return W
Wn = loadW('flow_W.json', 2)       # 2W
W4n = loadW('flow_W4.json', 4)     # 4 W4
def dig(c, i): return c // 8 ** i % 8
def law_terms(laws, l, m):
    return [(a, b, (-c if s else c)) for a, r in laws[(l, m)] for (b, c, s) in r]
def DA(laws, l, m, side, Win, j):
    """sum_i Win_{ji}(S) * d/dS_i A_l^(m) as dict (alpha, beta) -> int."""
    out = defaultdict(int)
    for a, b, c in law_terms(laws, l, m):
        for i in range(9):
            w = Win.get((j, i))
            if not w:
                continue
            d = dig(a if side == 'X' else b, i)
            if d == 0:
                continue
            for wc, wv in w.items():
                if side == 'X':
                    out[(a - 8 ** i + wc, b)] += c * d * wv
                else:
                    out[(a, b - 8 ** i + wc)] += c * d * wv
    return {k: v for k, v in out.items() if v}
def to_rows(poly):
    rows = defaultdict(list)
    for (a, b), v in sorted(poly.items()):
        rows[a].append((b, v))
    return sorted(rows.items())
def l1(poly): return sum(abs(v) for v in poly.values())
FAMILIES = {  # name: (m, side, Win, sin, chart c, Wout, sout, factor f)
    'E40': (0, 'X', W4n, 4, 0, Wn, 2, 4),
    'E44': (0, 'X', W4n, 4, 4, W4n, 4, 4),
    'E04': (0, 'X', Wn, 2, 4, W4n, 4, 0),
    'F4X': (4, 'X', W4n, 4, 4, W4n, 4, 4),
    'F4Y': (4, 'Y', W4n, 4, 4, W4n, 4, 4),
}
if __name__ == '__main__':
    laws = slots.load_laws()
    def lawl1(l, m): return sum(abs(c) for _, _, c in law_terms(laws, l, m))
    for name, (m, side, Win, sin, c, Wout, sout, f) in FAMILIES.items():
        mx = 0; sz = 0
        for j in (0, 1):
            D = {l: DA(laws, l, m, side, Win, j) for l in range(9)}
            for l in range(9):
                if l == c:
                    continue
                w = sout * lawl1(c, m) * l1(D[l]) + sout * lawl1(l, m) * l1(D[c])
                for code, coef in Wout.get((j, l), {}).items():
                    a = [i for i in range(9) for _ in range(dig(code, i))]
                    w += abs(sin * coef) * lawl1(a[0], m) * lawl1(a[1], m)
                mx = max(mx, w); sz = max(sz, len(D[l]))
        print(f'{name}: max wsum {mx} ({mx.bit_length()} bits), max |DA| terms {sz}')
