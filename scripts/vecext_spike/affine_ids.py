"""Affine identities for (b) (generic case x1 != x2), with cofactors w.r.t. the curve equations
hP : y1^2 = 4x1^3 - g2 x1 - g3, hQ likewise.  Integer-scaled laws (kappa' = 2 kappa).
E1_i: 4 d^2 lU = lW N3,        N3 = (y1-y2)^2 - 4(x1+x2) d^2,  d = x1 - x2
E2_i: 8 d^3 lV = lW Y3,        Y3 = -2(y1-y2)(N3 - 4 d^2 x1) - 8 d^3 y1
K1_ijk: d (kW' + 2 mu lW rho_lam + 2 lam lW rho_mu) = M lW (y1 - y2)
K3_ijk: 16 d^4 (kV' + 2 mu lV rho_lam + 2 lam lV rho_mu) = M lW (2 Y3 (y1 - y2) + 4 N3^2)
"""
import pickle
from common import *

L5 = pickle.load(open('laws5.pkl', 'rb'))
d = x1 - x2
N3 = (y1 - y2)**2 - 4*(x1 + x2)*d**2
Y3 = -2*(y1 - y2)*(N3 - 4*d**2*x1) - 8*d**3*y1
lamA = {'V': (y1, y2), 'W': (sp.Integer(1), sp.Integer(1))}
rhoA = {'V': (2*x1**2, 2*x2**2), 'W': (sp.Integer(0), sp.Integer(0))}
c1e = y1**2 - fcub(x1); c2e = y2**2 - fcub(x2)

def cofactors(diff):
    diff = sp.expand(diff)
    q1, r = sp.div(sp.Poly(diff, y1), sp.Poly(c1e, y1))
    q1 = q1.as_expr(); r = r.as_expr()
    q2, r2 = sp.div(sp.Poly(sp.expand(r), y2), sp.Poly(c2e, y2))
    q2 = q2.as_expr(); r2 = sp.expand(r2.as_expr())
    assert r2 == 0, 'nonzero remainder'
    assert sp.expand(q1*c1e + q2*c2e - diff) == 0
    return sp.expand(q1), sp.expand(q2)

out = {}
for i in (1, 2):
    lU, lV, lW = [aff(p) for p in LAWS[i]]
    out[('E1', i)] = cofactors(4*d**2*lU - lW*N3)
    out[('E2', i)] = cofactors(8*d**3*lV - lW*Y3)
    print('E', i, [len(sp.Add.make_args(q)) for q in out[('E1', i)] + out[('E2', i)]], flush=True)
for (i, lam, mu), D in L5.items():
    lU, lV, lW = [aff(p) for p in LAWS[i]]
    kW = aff(D['kW2']); kV = aff(D['kV2'])
    l1 = lamA[lam][0]; m2 = lamA[mu][1]; r1 = rhoA[lam][0]; r2 = rhoA[mu][1]
    M = l1*m2
    out[('K1', i, lam, mu)] = cofactors(d*(kW + 2*m2*lW*r1 + 2*l1*lW*r2) - M*lW*(y1 - y2))
    out[('K3', i, lam, mu)] = cofactors(16*d**4*(kV + 2*m2*lV*r1 + 2*l1*lV*r2)
                                        - M*lW*(2*Y3*(y1 - y2) + 4*N3**2))
    print('K', i, lam, mu, [len(sp.Add.make_args(q)) for q in out[('K1', i, lam, mu)] +
                            out[('K3', i, lam, mu)]], flush=True)
pickle.dump(out, open('affine.pkl', 'wb'))
