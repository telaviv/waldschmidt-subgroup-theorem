"""Numerical check (mod p) of A2's mixed forms E1_4 and E1_40: A_4 D A_l - A_l D A_4 = X0 * W4_jl(A), D = sum_i W_ji(X) d/dX_i
(input field W of chart 0, output chart 4), law 0. UNTRUSTED."""
import json, os, sys
import sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from g1_measure import load_laws, chart_pt, Xof, P
def load(fn):
    return {tuple(map(int, k.split(','))): {tuple(m): sp.Rational(c) for m, c in v}
            for k, v in json.load(open(os.path.join(HERE, fn))).items()}
W, W4 = load('flow_W.json'), load('flow_W4.json')
laws = load_laws()
Xs, Ys = sp.symbols('X0:9'), sp.symbols('Y0:9')
A = [sp.expand(sum(c * sp.prod([Xs[i] ** ex[i] for i in range(9)]) * sp.prod([Ys[i] ** ey[i] for i in range(9)])
                   for ex, ey, c in laws[(l, 0)])) for l in range(9)]
def Wq(WW, j, i, V): return sum(c * V[a] * V[b] for (a, b), c in WW.get((j, i), {}).items())
def fr(v): return int(v.p) * pow(int(v.q), -1, P) % P
import sys as _s
mode = _s.argv[1] if len(_s.argv) > 1 else '4'
Win, Wout, out, fac = (W, W4, 4, 0) if mode == '4' else (W4, W, 0, 4)
ok = 0; tot = 0
for j in (1, 2):
    D = lambda F: sp.expand(sum(sp.diff(F, Xs[i]) * Wq(Win, j, i, Xs) for i in range(9)))
    DA = [D(A[l]) for l in range(9)]
    for l in range(9):
        if l == out:
            continue
        H = sp.Poly(sp.expand(A[out] * DA[l] - A[l] * DA[out] - Xs[fac] * Wq(Wout, j, l, A)), *Xs, *Ys)
        good = all(fr(H.eval(tuple(Xof(chart_pt()[0]) + Xof(chart_pt()[0])))) == 0 for _ in range(3))
        ok += good; tot += 1
        print(f'mode {mode} j={j} l={l}: {"OK" if good else "FAIL"}', flush=True)
print(f'E1 mode {mode}: {ok}/{tot}')
