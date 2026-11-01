"""Chart-8 analogue of w4_check.py (first part): W8[j][i] with X0 * W8_ji = X8 W_ji - X_i W_j8 on A, quadratic
(interpolation mod p over the standard degree-2 monomials). UNTRUSTED. Writes flow_W8.json."""
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
W4 = {}  # (chart 8)
pts = [Xof(chart_pt()[0]) for _ in range(150)]
for j in (1, 2):
    for i in range(9):
        if i == 8:
            continue
        rows, rhs = [], []
        for X in pts:
            rows.append([X[a] * X[b] % P for a, b in std2])
            rhs.append(fr(sp.Rational(X[8] * Wv(j, i, X) - X[i] * Wv(j, 8, X))) if True else 0)
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
        print(f'W8_{j}{i} =', ' + '.join(f'{v}*X{a}X{b}' for (a, b), v in sol.items()))
json.dump({f'{j},{i}': [[list(k), str(v)] for k, v in W4[(j, i)].items()] for (j, i) in W4},
          open(os.path.join(HERE, 'flow_W8.json'), 'w'))
