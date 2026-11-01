"""M2.1 S3 (UNTRUSTED): the elements of I(V) not in J_V in low degree (exact over Q).

I(V)_d: the nullspace of the evaluation matrix of degree-d monomials at image points is computed EXACTLY over Q
using points of the image defined over Q (Mumford divisors from rational points?  -- not available in general), so we
proceed as follows: candidates F are found mod P (nullspace of the evaluation matrix in a weight block), lifted by
rational reconstruction, and then checked EXACTLY: F vanishes on the image iff F(X, T(X, tau)) = 0 identically
modulo the Mumford relations (sympy, exact).  Membership in J_V and in the colon ideals is exact (fmpq linear algebra).
Usage: python m2_excess.py D
"""
import sys, random
import flint
import sympy as sp
from m2_common import *
import jb_common as jb

D = int(sys.argv[1]) if len(sys.argv) > 1 else 3
rng = random.Random(11)


def ratrec(a, m=P):
    # rational reconstruction
    a %= m
    r0, r1, s0, s1 = m, a, 0, 1
    import math
    B = int(math.isqrt(m // 2))
    while r1 > B:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > B:
        return None
    from fractions import Fraction
    return Fraction(r1, s1) if s1 > 0 else Fraction(-r1, -s1)


# exact image parametrisation: affine Mumford chart + tau, sympy
s1, s2, b1, b0, tau = sp.symbols('s1 s2 b1 b0 tau')
import json, os
m = json.load(open(os.path.join(jb.SPIKE, 'model.json')))
env = {'s1': s1, 's2': s2, 'b1': b1, 'b0': b0}
Xm = [sp.sympify(e, locals=env) for e in m['X']]
GB = sp.groebner([sp.sympify(e, locals=env) for e in m['relations']], s1, s2, b1, b0, order='grevlex', domain='QQ')


def W1(c):
    if c == 0:
        return sp.Integer(0)
    p = jb.W[0][c]
    return sum(sp.Rational(int(cf.p), int(cf.q)) * sp.Mul(*[Xm[i] ** k for i, k in enumerate(e)]) for e, cf in p.to_dict().items())


Tm = {c: Xm[c] * tau - W1(c) / 3 for c in CH}
img = Xm + [Tm[0], Tm[4], Tm[8]]


def vanishes_exactly(F):
    e = sum(sp.Rational(int(c.p), int(c.q)) * sp.Mul(*[img[i] ** k for i, k in enumerate(ex)]) for ex, c in F.to_dict().items())
    e = sp.expand(e)
    pe = sp.Poly(e, tau)
    return all(GB.reduce(sp.expand(cf))[1] == 0 for cf in pe.coeffs())


pts = [V_point(rng) for _ in range(800)]
for w in range(10):
    rows = [e for e in monos(D) if wt_e(e) == w]
    M = flint.nmod_mat([[ev(mono(e), p) for e in rows] for p in pts[:len(rows) + 40]], P)
    # nullspace mod P: kernel of M (columns = monomials)
    Kmat, nul = M.nullspace()
    if nul == 0:
        continue
    # J_V part of this block
    cands = []
    for j in range(nul):
        vec = [int(Kmat[i, j]) for i in range(len(rows))]
        cands.append(vec)
    # reduce: find kernel elements not in J_V.  Build J_V,d block mod P, and test rank increase.
    cols = []
    for g in GV:
        if deg(g) > D:
            continue
        for e in monos(D - deg(g)):
            if (wt_e(e) + weight(g)) % 10 != w:
                continue
            pr = mono(e) * g
            cols.append([md(pr.to_dict().get(r, 0)) if r in pr.to_dict() else 0 for r in rows])
    J = flint.nmod_mat(cols, P) if cols else None
    rJ = J.rank() if J is not None else 0
    rK = nul
    print(f'weight {w}: dim I(V)_{D} block = {rK}, dim (J_V)_{D} block = {rJ}, excess = {rK - rJ}', flush=True)
    if rK > rJ:
        # find a kernel vector outside J: try each; take the RREF combos
        base = cols[:]
        for vec in cands:
            Mt = flint.nmod_mat(base + [vec], P)
            if Mt.rank() > (flint.nmod_mat(base, P).rank() if base else 0):
                # rational reconstruction after normalising the first nonzero entry to 1
                i0 = next(i for i, v in enumerate(vec) if v)
                inv = pow(vec[i0], P - 2, P)
                vec = [v * inv % P for v in vec]
                # sparsify by reducing modulo J (mod P) is skipped; reconstruct directly
                fr = [ratrec(v) for v in vec]
                if any(f is None for f in fr):
                    print('  ratrec failed'); break
                F = ZERO
                for e, f in zip(rows, fr):
                    if f:
                        F += flint.fmpq(f.numerator, f.denominator) * mono(e)
                ok = vanishes_exactly(F)
                print('  extra element (exact vanishing on the image:', ok, '), terms', nterms(F))
                print('   F =', F)
                inJ = member(F, GV) is not None
                print('   F in J_V (exact):', inJ)
                for c in CH:
                    print(f'   X{c}*F in J_V (exact):', member(X[c] * F, GV) is not None)
                for c in CH:
                    print(f'   T{c}*F in J_V (exact):', member(T[c] * F, GV) is not None)
                base.append(vec)
