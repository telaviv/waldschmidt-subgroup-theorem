"""M2.1 (UNTRUSTED, mod P): (1) tangency check of the chart-c derivation on V (validates the T_c flow from the
K-natural quadrics and the T_l (l != c) cubic R^{(c)}_{jl}); (2) does R/X_c agree on V with a quadric in (X, T)?
(3) does it agree with a quadric in X plus T_c * (linear) ... i.e. the full space of degree-2 forms.
delta X_a = W^{(c)}_{ja}/X_c,  delta T_c = 1/3 Q_{c,1j}/X_c,  delta T_l = R_{jl}/X_c^2   (homogeneous of degree 1).
"""
import random, json, os
import flint
import m2_common as mc
from m2_common import X, T, CH, GV, P, md, monos, mono, emb, ev
_src = open('m2_b5flow.py', encoding='utf8').read().splitlines()
exec(chr(10).join(_src[82:117]))
rng = random.Random(9)
inv = lambda a: pow(a % P, P - 2, P)
third = flint.fmpq(1, 3)
for c in CH:
    for j in (1, 2):
        R = {}
        for l in CH:
            if l != c:
                R[l] = T[c] * emb(mc.wfield(c)[j - 1][l]) + third * X[l] * Qc(c, j) - third * Dc(c, j, emb(mc.wfield(c)[0][l]))
        bad = 0
        for _ in range(4):
            pt = mc.scale(mc.V_point(rng), rng.randrange(1, P))
            xc = pt[c]
            dv = [ev(emb(mc.wfield(c)[j - 1][a]), pt) * inv(xc) % P for a in range(9)] + [0, 0, 0]
            dv[mc.TIDX[c]] = ev(third * Qc(c, j), pt) * inv(xc) % P
            for l in R:
                dv[mc.TIDX[l]] = ev(R[l], pt) * inv(xc * xc) % P
            for g in GV:
                s = sum(ev(g.derivative(v), pt) * dv[v] for v in range(12)) % P
                bad += (s != 0)
        # quadric fit: R_l / X_c = q on V ?
        fits = {}
        S2 = monos(2)
        pts = [mc.scale(mc.V_point(rng), rng.randrange(1, P)) for _ in range(150)]
        for l in R:
            rows = [[ev(mono(e), p) * p[c] % P for e in S2] + [(-ev(R[l], p)) % P] for p in pts]
            M = flint.nmod_mat(rows, P)
            Mq = flint.nmod_mat([r[:-1] for r in rows], P)
            fits[l] = (M.rank() == Mq.rank())
        print(f'chart {c}, j={j}: tangency violations {bad}/{4*len(GV)};  R_l = X_c * quadric on V: {fits}', flush=True)
