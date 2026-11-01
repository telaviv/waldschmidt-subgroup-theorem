"""Fibre half of the E^natural translation identity (STAGE5_MEV.md section 3).

For a law c = (i, j, k) (E-law, multipliers lambda = j, mu = k; 0 = V, 1 = W), a chart a of the
moving point P (normalized: P_a = 1) and a chart b of the sum A = NLaw_c(P, Q):

  E := 4 mu^2 L^2 Psi - (A_b D(kappa) - kappa D(A_b)) - 2 s rho_b(A_base)  in  (F(P), F(Q))

with L = law_i(P, Q)_b, A_b = 2 lambda mu L, kappa = kapW (b = W) / kapV (b = V),
D P = s c2_a(P) (abelian chart derivation, D Q = 0), Psi = lambda^2 2s rhohat_a(P) + eps_{a, lambda}.
Writes the cofactors to fibre_ids.pkl. Run from this folder.
"""
import pickle, sys, time
import sympy as sp
from defs import LAW, kapW, kapV, F, g2, g3, U1, V1, W1, U2, V2, W2

u, v, s, Q0, Q1, Q2 = sp.symbols('u v s Q0 Q1 Q2')
BI = {0: 1, 1: 2}

def setup(a):
    if a == 1:   # W chart: P = (u, v, 1)
        P = (u, v, sp.Integer(1))
        Du = s * 2 * v
        Dv = s * (12 * u**2 - g2)
    else:        # V chart: P = (u, 1, v)
        P = (u, sp.Integer(1), v)
        Du = s * (-2 * u * v * g2 - 1 - 3 * v**2 * g3)
        Dv = s * (-12 * u**2 + v**2 * g2)
    return P, Du, Dv

def expr(i, j, k, a, b):
    P, Du, Dv = setup(a)
    Q = (Q0, Q1, Q2)
    sub = {U1: P[0], V1: P[1], W1: P[2], U2: Q[0], V2: Q[1], W2: Q[2]}
    D = lambda f: sp.expand(sp.diff(f, u) * Du + sp.diff(f, v) * Dv)
    l = [sp.expand(LAW[i][c].subs(sub, simultaneous=True)) for c in range(3)]
    lam, mu = P[BI[j]], Q[BI[k]]
    L = l[BI[b]]
    kap = sp.expand((kapW(i, j, k) if b == 1 else kapV(i, j, k)).subs(sub, simultaneous=True))
    Ab = sp.expand(2 * lam * mu * L)
    A = [sp.expand(2 * lam * mu * x) for x in l]
    rho_b = A[0] * A[2] if b == 1 else 2 * g2 * A[0]**2 + 3 * g3 * A[0] * A[2]
    rhohat = u if a == 1 else 2 * g2 * u**2 + 3 * g3 * u * v
    if j == a:
        Psi = 2 * s * rhohat
    elif a == 1:   # lambda = V, P = (u, v, 1)
        Psi = v**2 * 2 * s * rhohat - (4 * u * v * Du - 2 * u**2 * Dv)
    else:          # a = V, lambda = W, P = (u, 1, v)
        Psi = v**2 * 2 * s * rhohat + (4 * u * v * Du - 2 * u**2 * Dv)
    E = 4 * mu**2 * L**2 * Psi - (Ab * D(kap) - kap * D(Ab)) - 2 * s * rho_b
    return sp.expand(E), P

def main():
    res = {}
    for i in range(2):
        for j in range(2):
            for k in range(2):
                for a in range(2):
                    for b in range(2):
                        t0 = time.time()
                        E, P = expr(i, j, k, a, b)
                        FP = sp.expand(F(*P))
                        FQ = sp.expand(F(Q0, Q1, Q2))
                        (q1, q2), r = sp.reduced(E, [FP, FQ], u, Q0, v, Q1, Q2, g2, g3, s,
                                                  order='lex')
                        ok = sp.expand(r) == 0
                        assert sp.expand(q1 * FP + q2 * FQ - E) == 0 or not ok
                        res[(i, j, k, a, b)] = (sp.expand(q1), sp.expand(q2), ok)
                        print(i, j, k, a, b, ok, len(sp.Add.make_args(sp.expand(q1))),
                              len(sp.Add.make_args(sp.expand(q2))), round(time.time() - t0, 1),
                              flush=True)
    pickle.dump(res, open('fibre_ids.pkl', 'wb'))

if __name__ == '__main__':
    main()
