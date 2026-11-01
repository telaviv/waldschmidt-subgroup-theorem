"""M2.1 S4 (UNTRUSTED; exact over Q): tau_0, the fibre coordinate of the identity.

(1) Data facts: W4C_{1,0}(e4) = W4C_{1,8}(e4) = 0, so theta_flow (chart 4, j = 1) at z = 0 gives d_1 theta_0(0) =
    d_1 theta_8(0) = 0, i.e. T(0, 0) = (0, -1/3 d_1 theta_4(0), 0) = theta_4(0) * (0, tau_0, 0).
(2) The model identity: for every m and chart c (c' = 4), the polarization law at Y = e4, U = (0, u, 0) is
        law^{m,c,4}(X, T; e4, (0,u,0)) = lambda_m X_c X_m (X; T + u X_{0,4,8})   modulo J_V,
    with lambda_m X_m X_k = Law_{m,k}(X, e4).  Checked by exact membership (degree 3, single copy).
    With law_eq at v = 0 (law(P, e_an) = kappa P) this forces tau_0 = 0.
Usage: python m2_tau0.py
"""
import json, os
from fractions import Fraction
import flint
import m2_common as mc
from m2_common import X, T, CH, GV, member, nterms, emb
import jb_common as jb

print('W4C_{1,0} =', jb.W4[0][0], ';  W4C_{1,8} =', jb.W4[0][8], ';  W4C_{2,8} =', jb.W4[1][8])
e4 = {4: 1}
def at_e4(p9):
    return p9.to_dict().get((0, 0, 0, 0, 2, 0, 0, 0, 0), 0)
print('values at e4 (coefficient of X4^2): W4C_{1,0}:', at_e4(jb.W4[0][0]), ' W4C_{1,8}:', at_e4(jb.W4[0][8]),
      ' W4C_{2,0}:', at_e4(jb.W4[1][0]), ' W4C_{2,8}:', at_e4(jb.W4[1][8]))

lq = json.load(open(os.path.join(jb.SPIKE, 'laws_Q.json')))
# Law_{m,k}(X, Y) restricted to Y = e4 + eps: need value and dLaw/dY_a at Y = e4
def law_terms(m, k):
    for e, cs in lq['laws'][f'{k},{m}']:
        c = Fraction(cs)
        yield tuple(e[:9]), tuple(e[9:]), flint.fmpq(c.numerator, c.denominator)

def xpoly(ex, c):
    return c * mc.mono(tuple(ex) + (0, 0, 0))

third = flint.fmpq(1, 3); sixth = flint.fmpq(1, 6)
W4e = [at_e4(jb.W4[0][a]) for a in range(9)]   # W^{(4)}_{1a}(e4)
print('W^{(4)}_{1a}(e4) =', [str(v) for v in W4e])
tot = 0
for m in range(9):
    for c in CH:
        # Law(X, e4), dLaw/dY_a (X, e4)
        val = {k: mc.ZERO for k in range(9)}
        dy = {k: [mc.ZERO] * 9 for k in range(9)}
        for k in range(9):
            for ex, ey, cf in law_terms(m, k):
                if ey == (0, 0, 0, 0, 2, 0, 0, 0, 0):
                    val[k] += xpoly(ex, cf)
                for a in range(9):
                    if ey[a] >= 1:
                        ey2 = list(ey); ey2[a] -= 1
                        if tuple(ey2) == (0, 0, 0, 0, 1, 0, 0, 0, 0) or (a == 4 and ey == (0, 0, 0, 0, 2, 0, 0, 0, 0)):
                            dy[k][a] += xpoly(ex, cf * ey[a])
        # lambda_m: Law(X, e4) = lambda X_m X_k ?
        lam = val[0].to_dict().get(tuple(1 if i in (m, 0) and m != 0 else (2 if i == 0 and m == 0 else 0) for i in range(12)), None) if val[0] != 0 else None
        lamk = None
        for k in range(9):
            if val[k] != 0:
                q = val[k]
                # find lambda from X_m X_k coefficient
                e = [0] * 12; e[m] += 1; e[k] += 1
                lamk = q.to_dict().get(tuple(e))
                break
        ok_val = all(val[k] == lamk * X[m] * X[k] for k in range(9)) if lamk is not None else None
        # T-law at (e4, U = 0), c' = 4
        Dc = lambda L: sum((emb(mc.wfield(c)[0][a]) * L.derivative(a) for a in range(9)), mc.ZERO)
        res = []
        sizes = []
        for k in CH:
            DY = sum((W4e[a] * dy[k][a] for a in range(9)), mc.ZERO)
            Tlaw = T[c] * val[k] - sixth * (Dc(val[k]) + X[c] * DY)
            target = lamk * X[c] * X[m] * T[k] if lamk is not None else mc.ZERO
            cof = member(Tlaw - target, GV)
            res.append(cof is not None)
            sizes.append(sum(nterms(x) for x in cof) if cof else None)
        tot += sum(s for s in sizes if s)
        print(f'm={m} c={c}: Law(X,e4) = {lamk}*X_m*X_k: {ok_val};  T-law(X,T; e4, 0) - lambda X_c X_m T_k in J_V: {res}, cofactor terms {sizes}', flush=True)
print('total cofactor terms (all m, c):', tot)
