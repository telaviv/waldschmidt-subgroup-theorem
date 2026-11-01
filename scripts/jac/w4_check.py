"""Numerical checks (mod p) for the chart-4 flow and the law-4 equivariance (E1 for m = 4, both arguments, chart 0
and chart 4). Finds W4[j][i] (doubled: W4n = 2 W^(4)) with X0 * W4_ji = X4 W_ji - X_i W_j4 on A, as a quadratic
form (interpolation over the 36 standard degree-2 monomials). UNTRUSTED. Writes flow_W4.json."""
import json, os, sys
import flint, sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from g1_measure import load_laws, chart_pt, Xof, P, ratrec
SPIKE = os.path.join(HERE, '..', 'abvar_spike')
lq = json.load(open(os.path.join(SPIKE, 'laws_Q.json')))
std2 = [tuple(s) for s in lq['std']]
W = {tuple(map(int, k.split(','))): {tuple(m): sp.Rational(c) for m, c in v}
     for k, v in json.load(open(os.path.join(HERE, 'flow_W.json'))).items()}
def Wv(j, i, X):   # W (not doubled), j in 1,2
    return sum(c * X[a] * X[b] for (a, b), c in W.get((j, i), {}).items()) if i > 0 else 0
def fr(c): return int(c.p) * pow(int(c.q), -1, P) % P
W4 = {}
pts = [Xof(chart_pt()[0]) for _ in range(150)]
for j in (1, 2):
    for i in range(9):
        if i == 4:
            continue
        rows, rhs = [], []
        for X in pts:
            rows.append([X[a] * X[b] % P for a, b in std2])
            rhs.append(fr(sp.Rational(X[4] * Wv(j, i, X) - X[i] * Wv(j, 4, X))) if True else 0)
        M = flint.nmod_mat([r + [v] for r, v in zip(rows, rhs)], P)
        R, rk = M.rref()
        _, rkA = flint.nmod_mat(rows, P).rref()
        assert rk == rkA, ('W4 not quadratic', j, i)
        sol = {}
        for r in range(rk):
            piv = next(c for c in range(len(std2)) if int(R[r, c]) != 0)
            v = ratrec(int(R[r, len(std2)]))
            if v != 0:
                sol[std2[piv]] = v
        W4[(j, i)] = sol
        print(f'W4_{j}{i} =', ' + '.join(f'{v}*X{a}X{b}' for (a, b), v in sol.items()))
json.dump({f'{j},{i}': [[list(k), str(v)] for k, v in W4[(j, i)].items()] for (j, i) in W4},
          open(os.path.join(HERE, 'flow_W4.json'), 'w'))
# E1-type checks
laws = load_laws()
Xs, Ys = sp.symbols('X0:9'), sp.symbols('Y0:9')
def A(l, m): return sp.expand(sum(c * sp.prod([Xs[i] ** ex[i] for i in range(9)]) * sp.prod([Ys[i] ** ey[i] for i in range(9)]) for ex, ey, c in laws[(l, m)]))
def Wq(WW, j, i, V): return sum(c * V[a] * V[b] for (a, b), c in WW.get((j, i), {}).items())
def check(WW, chart, m, side, j, l, Am):
    V = Xs if side == 'X' else Ys
    D = lambda F: sp.expand(sum(sp.diff(F, V[i]) * Wq(WW, j, i, V) for i in range(9) if i != chart))
    lhs = Am[chart] * D(Am[l]) - Am[l] * D(Am[chart])
    rhs = V[chart] * Wq(WW, j, l, Am)
    H = sp.Poly(sp.expand(lhs - rhs), *Xs, *Ys)
    for _ in range(2):
        cP, _ = chart_pt(); cQ, _ = chart_pt()
        v = H.eval(tuple(Xof(cP) + Xof(cQ)))
        if fr(v) != 0:
            return False
    return True
for m in (0, 4):
    Am = [A(l, m) for l in range(9)]
    for chart, WW in ((0, W), (4, W4)):
        for side in ('X', 'Y'):
            if m == 0 and side == 'Y':
                continue
            res = [check(WW, chart, m, side, j, l, Am) for j in (1, 2) for l in range(9) if l != chart]
            print(f'law {m}, chart X{chart}, {side}-flow: {sum(res)}/{len(res)} identities vanish at random pairs')
