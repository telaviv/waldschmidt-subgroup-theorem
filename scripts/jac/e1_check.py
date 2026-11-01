"""Numerical check (mod p) of the equivariance identities (E1), bidegree (5,4):
   A_0 * D_j A_l - A_l * D_j A_0 = X_0 * W_jl(A),   D_j F = sum_i W_ji(X) dF/dX_i   (X-side flow only).
UNTRUSTED measurement."""
import json, os, sys, random
import sympy as sp
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from g1_measure import load_laws, chart_pt, Xof, P
laws = load_laws()
W = {tuple(map(int, k.split(','))): {tuple(m): sp.Rational(c) for m, c in v} for k, v in json.load(open(os.path.join(HERE, 'flow_W.json'))).items()}
Xs, Ys = sp.symbols('X0:9'), sp.symbols('Y0:9')
A = [sp.expand(sum(c * sp.prod([Xs[i] ** ex[i] for i in range(9)]) * sp.prod([Ys[i] ** ey[i] for i in range(9)])
                   for ex, ey, c in laws[(l, 0)])) for l in range(9)]
def Wq(j, i, V):
    return sum(v * V[a] * V[b] for (a, b), v in W.get((j, i), {}).items())
tot = 0
for j in (1, 2):
    DA = [sp.expand(sum(sp.diff(A[l], Xs[i]) * Wq(j, i, Xs) for i in range(1, 9))) for l in range(9)]
    for l in range(1, 9):
        lhs = A[0] * DA[l] - A[l] * DA[0]
        rhs = Xs[0] * Wq(j, l, A)
        good = 0
        for _ in range(4):
            cP, _ = chart_pt(); cQ, _ = chart_pt()
            vals = tuple(Xof(cP) + Xof(cQ))
            v = sp.Poly(lhs - rhs, *Xs, *Ys).eval(vals)
            good += (int(v.p) * pow(int(v.q), -1, P)) % P == 0
        n1 = len(sp.Add.make_args(sp.expand(A[0]))) * len(sp.Add.make_args(DA[l])) + \
             len(sp.Add.make_args(sp.expand(A[l]))) * len(sp.Add.make_args(DA[0]))
        tot += n1
        print(f'E1[j={j}, l={l}]: zero at {good}/4 random pairs; D A_l {len(sp.Add.make_args(DA[l]))} terms; '
              f'~{n1} term-pairs (+ W(A))', flush=True)
print('total term-pairs', tot)
