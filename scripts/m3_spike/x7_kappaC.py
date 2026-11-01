"""M3 spike (untrusted, numerical): the period lifts of lean_mstar's propX7_K and their complex rank.

Reproduces, coordinate for coordinate, the 2n = 12r period lifts that propX7_K feeds to frameX_false
(lean_mstar CM4E/AbVar/X7.lean, ll. 391-396):
   X_A(h) = aGen 0 h.1 h.2 perT + aLift 2 5 (coords(theta_h * beta)) perT
   X_B(h) = eLift (coords theta_h) omega7 + aLift 1 4 (coords(theta_h * beta / mu7')) perT
in T(A^{3r} x E^{3r}) = C^{9r} x C^{3r} (QX7 r), h in Fin r x Fin 6, theta(j,e) = zeta^e b_j.
Checks: (1) every lift lies in V'' (mu2 = sigma * mu1, sigma = beta P3 / P1, using relation_R);
(2) Q-rank 12r (exact, from the rational coordinates is automatic) and complex rank (SVD): expected 4r + 4r = 8r.
Fields: r = 1, K = Q(zeta7), b = (1); r = 3, K = Q(zeta7, 2^(1/3)), b = (1, c, c^2).
"""
import itertools
import mpmath as mp
import sympy as sp

mp.mp.dps = 50
Z, C = sp.symbols('Z C')
PHI = sp.Poly(sum(Z ** k for k in range(7)), Z)

z = mp.exp(2j * mp.pi / 7)
alpha = z + z ** 2 + z ** 4
mu7 = 1 + z + z ** 6
mu7p = (1 - z) * (1 - z ** 2) * mu7 / (1 - z ** 3)


def perA(j):
    k = mp.mpf(j) / 7
    return (1 - z ** j) * mp.beta(k, k)


perT = [perA(s + 1) for s in range(3)]
omega = mp.beta(mp.mpf(1) / 7, mp.mpf(2) / 7)
assert abs(perA(1) * perA(2) - mu7p * perA(3) * omega) < mp.mpf(10) ** -40   # relation_R

zp = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [0, -1, -1], [-1, -1, -1]]
zq = [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 1, 1], [1, 0, 0], [0, 0, -1]]


def run(r, beta_expr):
    # K = Q(Z) (r = 1) or Q(Z, C), C^3 = 2 (r = 3); basis theta(j, e) = Z^e C^j
    def red(expr):
        expr = sp.expand(expr)
        if r == 3:
            expr = sp.rem(sp.Poly(expr, C), sp.Poly(C ** 3 - 2, C)).as_expr()
        p = sp.Poly(sp.expand(expr), Z)
        return sp.expand(sp.rem(p, PHI).as_expr())

    def coords(expr):
        e = red(expr)
        out = {}
        for j in range(r):
            for ee in range(6):
                term = sp.Poly(e, Z, C).coeff_monomial(Z ** ee * C ** j) if r == 3 else \
                    sp.Poly(e, Z).coeff_monomial(Z ** ee)
                out[(j, ee)] = sp.Rational(term)
        return out

    def num(expr):  # evaluate an element of K numerically
        c = mp.cbrt(2)
        f = sp.lambdify((Z, C), expr, 'mpmath')
        return f(z, c)

    # mu7' as an element of K: invert via the numerical value? use exact: mu7' = (1-Z)(1-Z^2)(1+Z+Z^6)/(1-Z^3)
    inv13 = sp.invert(sp.Poly(1 - Z ** 3, Z), PHI).as_expr()
    mu7p_K = red((1 - Z) * (1 - Z ** 2) * (1 + Z + Z ** 6) * inv13)
    assert abs(num(mu7p_K) - mu7p) < 1e-30
    mu7p_inv = sp.invert(sp.Poly(mu7p_K, Z), PHI).as_expr()
    beta = beta_expr
    dimA, dimE = 9 * r, 3 * r

    def idxA(t, s, j):
        return (t * 3 + s) * r + j

    def idxE(j, e):
        return dimA + j * 3 + e

    def aGen(t, j, e, v):
        x = [mp.mpc(0)] * (dimA + dimE)
        for s in range(3):
            x[idxA(t, s, j)] = z ** ((s + 1) * e) * v[s]
        return x

    def add(x, y):
        return [a + b for a, b in zip(x, y)]

    def scal(c, x):
        return [c * a for a in x]

    def aLift(t, mt, m, v):
        x = [mp.mpc(0)] * (dimA + dimE)
        for (j, e), q in m.items():
            if q != 0:
                x = add(x, scal(mp.mpf(q.p) / q.q, aGen(t, j, mt * e, v)))
        return x

    def eLift(m, u):
        x = [mp.mpc(0)] * (dimA + dimE)
        for (j, e), q in m.items():
            qf = mp.mpf(q.p) / q.q
            for e2 in range(3):
                x[idxE(j, e2)] += qf * zp[e][e2] * u + qf * zq[e][e2] * alpha * u
        return x

    bvals = [num(C ** j) for j in range(r)]

    def mu1(x):
        return sum(bvals[j] * x[idxA(0, 0, j)] for j in range(r)) + \
            sum(z ** e * bvals[j] * x[idxE(j, e)] for j in range(r) for e in range(3))

    def mu2(x):
        return sum(bvals[j] * x[idxA(2, 2, j)] for j in range(r)) + sum(bvals[j] * x[idxA(1, 1, j)] for j in range(r))

    betan = num(beta)
    sigma = betan * perA(3) / perA(1)
    lifts_A, lifts_B = [], []
    for j, e in itertools.product(range(r), range(6)):
        th = Z ** e * C ** j
        XA = add(aGen(0, j, e, perT), aLift(2, 5, coords(th * beta), perT))
        XB = add(eLift(coords(th), omega), aLift(1, 4, coords(th * beta * mu7p_inv), perT))
        lifts_A.append(XA)
        lifts_B.append(XB)
    dev = max(abs(mu2(x) - sigma * mu1(x)) for x in lifts_A + lifts_B)
    print(f"r = {r}, beta = {beta}: max |mu2 - sigma mu1| over lifts = {mp.nstr(dev, 3)}")

    def crank(vs, tol=mp.mpf(10) ** -25):
        M = mp.matrix(len(vs), len(vs[0]))
        for i, v in enumerate(vs):
            for k, a in enumerate(v):
                M[i, k] = a
        S = mp.svd_c(M, compute_uv=False)
        sv = sorted([abs(s) for s in S], reverse=True)
        return sum(1 for s in sv if s > tol), sv

    rA, _ = crank(lifts_A)
    rB, _ = crank(lifts_B)
    rAB, sv = crank(lifts_A + lifts_B)
    print(f"  complex rank: X_A {rA} (expected {4*r}), X_B {rB} (expected {4*r}), all {rAB} (expected {8*r}); "
          f"Q-rank {12*r}")
    print(f"  (5.4) premise with kappa_C: 18r > 24r + 4 - kappa_C  <=>  {18*r} > {24*r + 4 - rAB}: "
          f"{18*r > 24*r + 4 - rAB};  with d2 = 12r (no G_a^2 in d2): {18*r} > {24*r - rAB}: {18*r > 24*r - rAB}")


run(1, sp.Integer(1))
run(1, 2 + Z)
run(3, 1 + C)
