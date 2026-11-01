"""Compute the fibre corrections kappa^W, kappa^V (bidegree (3,3) forms in E-variables) for the
5-variable model (U,V,W,T1,T3), laws i in {1,2}, multipliers lam, mu in {V, W}.

A^{(i,lam,mu)} = (M lawU, M lawV, M lawW,
                  mu2 lawW T_lam(P) + lam1 lawW T_mu(Q) - kW,
                  mu2 lawV T_lam(P) + lam1 lawV T_mu(Q) - kV),   M = lam(P) mu(Q),
T_W = T1, T_V = T3;  lam t = T_lam + rho_lam,  rho_W = 0, rho_V = 2U^2/W.
"""
import pickle, sys
from common import *

CUB = lambda U, V, W: [V**3, V**2*U, V**2*W, V*U**2, V*U*W, V*W**2, U**2*W, U*W**2, W**3]
B1 = [aff(m) for m in CUB(U1, V1, W1)]
B2 = [aff(m) for m in CUB(U2, V2, W2)]
HB1 = CUB(U1, V1, W1)
HB2 = CUB(U2, V2, W2)

def lamaff(name, which):
    if name == 'W':
        return sp.Integer(1)
    return y1 if which == 1 else y2

def rhoaff(name, which):
    if name == 'W':
        return sp.Integer(0)
    return 2*x1**2 if which == 1 else 2*x2**2

def solve_kappa(N, D):
    """kappa * D == N mod curves, kappa in span(B1 x B2) with weighted coefficients."""
    N = nf(N); D = nf(D)
    wN = wdeg_set(N); wD = wdeg_set(D)
    assert len(wN) == 1 and len(wD) == 1, (wN, wD)
    wk = list(wN)[0] - list(wD)[0]
    terms, labels = [], []
    for k, b1 in enumerate(B1):
        for l, b2 in enumerate(B2):
            wb = list(wdeg_set(b1*b2))[0]
            for gm in gmonos(wk - wb):
                terms.append(nf(gm*b1*b2*D))
                labels.append((k, l, gm))
    sol = solve_linear(terms, N, [x1, y1, x2, y2, g2, g3])
    assert sol is not None, "no solution"
    kap = 0
    for r, (k, l, gm) in zip(sol, labels):
        if r != 0:
            kap += r*gm*HB1[k]*HB2[l]
    return sp.expand(kap), wk

c_num = (y1 - y2)  # c = c_num / (2 (x1 - x2))
res = {}
for i in (1, 2):
    lU, lV, lW = [aff(p) for p in LAWS[i]]
    for lam in 'VW':
        for mu in 'VW':
            l1 = lamaff(lam, 1); m2 = lamaff(mu, 2)
            r1 = rhoaff(lam, 1); r2 = rhoaff(mu, 2)
            # kW = l1 m2 lW c - m2 lW r1 - l1 lW r2
            D = 2*(x1 - x2)
            N = l1*m2*lW*c_num - D*(m2*lW*r1 + l1*lW*r2)
            kW, w1 = solve_kappa(N, D)
            # kV = l1 m2 (lV c + 2 lU^2/lW) - m2 lV r1 - l1 lV r2
            D2 = 2*(x1 - x2)*lW
            N2 = l1*m2*(lV*c_num*lW + 4*(x1 - x2)*lU**2) - D2*(m2*lV*r1 + l1*lV*r2)
            kV, w2 = solve_kappa(N2, D2)
            res[(i, lam, mu)] = (kW, kV)
            print(i, lam, mu, 'weights', w1, w2, 'terms', len(sp.Add.make_args(kW)),
                  len(sp.Add.make_args(kV)), flush=True)
pickle.dump(res, open('kappa.pkl', 'wb'))
