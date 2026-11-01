"""A4 spike (UNTRUSTED, mod p): polynomial chart fields for every chart c of Grant's P^8 model, and a cover of A.

1. For each chart c in 0..8 and j in {1,2}, look for quadratic forms W^[c]_{ji} with
       X_0 * W^[c]_{ji} = X_c * W_{ji} - X_i * W_{jc}      on A
   (W = chart-0 field of scripts/jac/flow_W.json, W_{j0} = 0), by interpolation over the 36 standard degree-2
   monomials at random affine points of A.  (c = 4 reproduces flow_W4.json.)
Result (2026-10-31, p = 1000003): all 9 charts have a quadratic field (27-51 standard-monomial terms per chart).
Since every nonzero X has some X_c != 0, the 9 chart fields cover A; no cover computation is needed.
Usage: python charts_modp.py
"""
import json, os, sys, random
import flint, sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
JAC = os.path.join(HERE, '..', 'jac')
sys.path.insert(0, JAC)
from g1_measure import chart_pt, Xof, P, ratrec
SPIKE = os.path.join(HERE, '..', 'abvar_spike')
lq = json.load(open(os.path.join(SPIKE, 'laws_Q.json')))
std2 = [tuple(s) for s in lq['std']]
W = {tuple(map(int, k.split(','))): {tuple(m): sp.Rational(c) for m, c in v}
     for k, v in json.load(open(os.path.join(JAC, 'flow_W.json'))).items()}


def fr(c):
    c = sp.Rational(c)
    return int(c.p) * pow(int(c.q), -1, P) % P


def Wv(j, i, X):
    if i == 0:
        return 0
    return sum(fr(c) * X[a] * X[b] for (a, b), c in W.get((j, i), {}).items()) % P


random.seed(11)
pts = [Xof(chart_pt()[0]) for _ in range(160)]
rowsA = [[X[a] * X[b] % P for a, b in std2] for X in pts]
_, rkA = flint.nmod_mat(rowsA, P).rref()
res = {}
for c in range(9):
    ok = True
    nterms = 0
    for j in (1, 2):
        for i in range(9):
            rhs = [(X[c] * Wv(j, i, X) - X[i] * Wv(j, c, X)) % P for X in pts]
            M = flint.nmod_mat([r + [v] for r, v in zip(rowsA, rhs)], P)
            _, rk = M.rref()
            if rk != rkA:
                ok = False
            else:
                R, _ = M.rref()
                nterms += sum(1 for r in range(rk) if int(R[r, len(std2)]) != 0)
    res[c] = ok
    print(f'chart X{c}: quadratic chart field exists on A: {ok}' + (f' ({nterms} nonzero std-monomial terms)' if ok else ''),
          flush=True)

# (Part 2, the Theta cover, is unnecessary: every chart has a quadratic field, and X != 0 has some X_c != 0.)
