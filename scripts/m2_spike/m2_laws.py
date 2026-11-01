"""M2.1 S5/S4 (UNTRUSTED): the (3,3) polarization laws of the (M-a) model, their sizes, and mod-p checks.

Laws (M2.md 2.3).  Law_{m,k}(X, Y) = A_k^{(m)} (laws_Q.json, bidegree (2,2)).  For charts c, c' in {0,4,8}:
  X-part   L^{m,c,c'}_k     = X_c Y_c' Law_{m,k}                                     (k = 0..8)
  T-part   L^{m,c,c'}_{T_k} = Y_c' T_c Law_{m,k} + X_c U_c' Law_{m,k}
                              - 1/6 ( Y_c' D^X_c Law_{m,k} + X_c D^Y_c' Law_{m,k} )   (k = 0, 4, 8)
  with D^X_c L = sum_a W^{(c)}_{1a}(X) dL/dX_a, D^Y_c' likewise in Y (W^{(0)} = flowW, W^{(4)} = W4C, W^{(8)} = W8C).
  This is 1/2 (sum_a dLaw/dX_a T_a + sum_a dLaw/dY_a U_a) * X_c Y_c' with T_a = (X_a T_c - 1/3 W^{(c)}_{1a})/X_c and
  Euler's identity.  Variables: X0..X8, T0, T4, T8, Y0..Y8, U0, U4, U8 (24).
Checks mod P at random points of the image (Numerical):
  (a) the 81 outputs are pairwise proportional (rank 1) and lie on V (all 15 generators vanish);
  (b) neutral element: Q = (e4; 0, 0, 0) gives P; Q = (e4; 0, t, 0) gives the fibre translate (X; T + t X_{0,4,8});
      so the identity of the model group has T = 0 (tau_0 = 0) and is the unique neutral element on the fibre;
  (c) commutativity, associativity, inverse [-1](X, T) = (negP X; -T0, T4, -T8).
Also the explicit expanded polynomials: term counts per coordinate (S5), and a spot check of the expansion.
Usage: python m2_laws.py
"""
import json
import os
import random
import time
from fractions import Fraction

import flint

import m2_common as mc
from m2_common import P, md, CH
import jb_common as jb

N24 = tuple(f'X{i}' for i in range(9)) + ('T0', 'T4', 'T8') + tuple(f'Y{i}' for i in range(9)) + ('U0', 'U4', 'U8')
c24 = flint.fmpq_mpoly_ctx.get(N24, 'degrevlex')
G24 = c24.gens()
Xv, Tv, Yv, Uv = G24[:9], dict(zip(CH, G24[9:12])), G24[12:21], dict(zip(CH, G24[21:24]))
ZERO = c24.from_dict({})

lq = json.load(open(os.path.join(jb.SPIKE, 'laws_Q.json')))


def law(m, k):
    d = {}
    for e, cs in lq['laws'][f'{k},{m}']:
        c = Fraction(cs)
        d[tuple(e[:9]) + (0, 0, 0) + tuple(e[9:]) + (0, 0, 0)] = flint.fmpq(c.numerator, c.denominator)
    return c24.from_dict(d)


def W9to(p9, side):
    """embed a 9-var polynomial in X (side 0) or Y (side 1)"""
    off = 0 if side == 0 else 12
    d = {}
    for e, c in p9.to_dict().items():
        ee = [0] * 24
        for i in range(9):
            ee[off + i] = e[i]
        d[tuple(ee)] = c
    return c24.from_dict(d)


WF = {c: [W9to(mc.wfield(c)[0][a], 0) for a in range(9)] for c in CH}
WFY = {c: [W9to(mc.wfield(c)[0][a], 1) for a in range(9)] for c in CH}


def DX(c, L):
    r = ZERO
    for a in range(9):
        if WF[c][a] != 0:
            r += WF[c][a] * L.derivative(a)
    return r


def DY(c, L):
    r = ZERO
    for a in range(9):
        if WFY[c][a] != 0:
            r += WFY[c][a] * L.derivative(12 + a)
    return r


sixth = flint.fmpq(1, 6)


def laws_33(m, c, cp):
    out = []
    for k in range(9):
        out.append(Xv[c] * Yv[cp] * law(m, k))
    for k in CH:
        L = law(m, k)
        out.append(Yv[cp] * Tv[c] * L + Xv[c] * Uv[cp] * L - sixth * (Yv[cp] * DX(c, L) + Xv[c] * DY(cp, L)))
    return out


def nt(p):
    return len(p.to_dict())


# ----------------------------------------------------------------------------- fast structured evaluation mod P
LAWD = {(m, k): [(tuple(e), md(Fraction(cs))) for e, cs in lq['laws'][f'{k},{m}']] for m in range(9) for k in range(9)}
WD = {c: [[(e, md(cf)) for e, cf in mc.wfield(c)[0][a].to_dict().items()] for a in range(9)] for c in CH}


def ev9(terms, x):
    s = 0
    for e, c in terms:
        t = c
        for i, k in enumerate(e):
            if k:
                t = t * pow(x[i], k, P) % P
        s += t
    return s % P


_LG = {}


def law_grad(m, k, x, y):
    key = (m, k, tuple(x), tuple(y))
    if key not in _LG:
        _LG[key] = _law_grad(m, k, x, y)
    return _LG[key]


def _law_grad(m, k, x, y):
    """value, d/dX_a, d/dY_a of Law_{m,k} at (x, y)"""
    val = 0
    gx = [0] * 9
    gy = [0] * 9
    for e, c in LAWD[(m, k)]:
        mon = [pow(x[i], e[i], P) for i in range(9)] + [pow(y[i], e[9 + i], P) for i in range(9)]
        full = c
        for v in mon:
            full = full * v % P
        val += full
        for a in range(9):
            if e[a]:
                t = c * e[a] % P
                for i in range(18):
                    t = t * (pow(x[i], e[i] - (1 if i == a else 0), P) if i < 9 else mon[i]) % P
                gx[a] += t
            if e[9 + a]:
                t = c * e[9 + a] % P
                for i in range(18):
                    t = t * (mon[i] if i < 9 else pow(y[i - 9], e[i] - (1 if i - 9 == a else 0), P)) % P
                gy[a] += t
    return val % P, [g % P for g in gx], [g % P for g in gy]


i6 = pow(6, P - 2, P)


def eval_law(m, c, cp, Pt, Qt):
    x, tt = Pt[:9], dict(zip(CH, Pt[9:]))
    y, uu = Qt[:9], dict(zip(CH, Qt[9:]))
    wx = [ev9(WD[c][a], x) for a in range(9)]
    wy = [ev9(WD[cp][a], y) for a in range(9)]
    out = []
    lg = {}
    for k in range(9):
        lg[k] = law_grad(m, k, x, y)
        out.append(x[c] * y[cp] % P * lg[k][0] % P)
    for k in CH:
        L, gx, gy = lg[k]
        dx = sum(wx[a] * gx[a] for a in range(9)) % P
        dy = sum(wy[a] * gy[a] for a in range(9)) % P
        out.append((y[cp] * tt[c] % P * L + x[c] * uu[cp] % P * L - i6 * (y[cp] * dx + x[c] * dy)) % P)
    return out


def proportional(a, b):
    return all((a[i] * b[j] - a[j] * b[i]) % P == 0 for i in range(len(a)) for j in range(len(a)))


def nz(v):
    return any(v)


def add(Pt, Qt, combos=((0, 0, 0), (0, 4, 4), (4, 0, 8), (0, 8, 0))):
    for m, c, cp in combos:
        o = eval_law(m, c, cp, Pt, Qt)
        if nz(o):
            return o
    for m in range(9):
        for c in CH:
            for cp in CH:
                o = eval_law(m, c, cp, Pt, Qt)
                if nz(o):
                    return o
    raise ValueError('all laws vanish')


def onV(pt):
    return all(mc.ev(g, pt) == 0 for g in mc.GV)


def neg(pt):
    s = [1, 1, 1, 1, -1, -1, -1, -1, 1]
    return [(s[i] * pt[i]) % P for i in range(9)] + [(-pt[9]) % P, pt[10], (-pt[11]) % P]


if __name__ == '__main__':
    t0 = time.time()
    rng = random.Random(5)
    print('== (a) all 81 laws at random pairs: rank one, output on V ==')
    for trial in range(3):
        Pt, Qt = mc.V_point(rng), mc.scale(mc.V_point(rng), rng.randrange(1, P))
        outs = [eval_law(m, c, cp, Pt, Qt) for m in range(9) for c in CH for cp in CH]
        nzo = [o for o in outs if nz(o)]
        ok = all(proportional(nzo[0], o) for o in nzo)
        print(f'trial {trial}: nonzero laws {len(nzo)}/81, pairwise proportional: {ok}, output on V: {onV(nzo[0])}',
              flush=True)
    print('\n== (b) neutral element and fibre translation ==')
    e4 = [0, 0, 0, 0, 1, 0, 0, 0, 0]
    for trial in range(2):
        Pt = mc.V_point(rng)
        o = add(Pt, e4 + [0, 0, 0])
        print(' law(P, (e4;0,0,0)) ∝ P:', proportional(o, Pt))
        t = rng.randrange(1, P)
        o = add(Pt, e4 + [0, t, 0])
        Pt_t = Pt[:9] + [(Pt[9] + t * Pt[0]) % P, (Pt[10] + t * Pt[4]) % P, (Pt[11] + t * Pt[8]) % P]
        print(' law(P, (e4;0,t,0)) ∝ (X; T + t X_c):', proportional(o, Pt_t), '  ∝ P:', proportional(o, Pt))
        print(' (e4; t, 0, 0) is not on V for t != 0 (P04 = -t):', not onV(e4 + [t, 0, 0]))
    print('\n== (c) commutativity, associativity, inverse ==')
    for trial in range(2):
        A_, B_, C_ = mc.V_point(rng), mc.V_point(rng), mc.V_point(rng)
        print(' commutative:', proportional(add(A_, B_), add(B_, A_)))
        print(' associative:', proportional(add(add(A_, B_), C_), add(A_, add(B_, C_))))
        print(' inverse  P + [-1]P ∝ (e4;0,0,0):', proportional(add(A_, neg(A_)), e4 + [0, 0, 0]),
              ' [-1]P on V:', onV(neg(A_)))
    print(f'[{time.time() - t0:.0f}s]', flush=True)

    print('\n== S5: sizes of the expanded (3,3) laws (terms per coordinate) ==')
    tot = 0
    totX = totT = 0
    maxT = 0
    per = {}
    spot = None
    for m in range(9):
        for c in CH:
            for cp in CH:
                L = laws_33(m, c, cp)
                sz = [nt(p) for p in L]
                per[f'{m},{c},{cp}'] = sz
                totX += sum(sz[:9]); totT += sum(sz[9:]); maxT = max(maxT, max(sz[9:]))
                if spot is None:
                    spot = (m, c, cp, L)
    print(f'X-parts: {totX} terms over 81x9 coordinates (= 9 x the 8235 law terms); T-parts: {totT} terms over 81x3'
          f' coordinates, max {maxT} per coordinate; total {totX + totT}')
    for key in ['0,0,0', '4,4,4', '0,4,8', '8,8,8']:
        print('  law', key, 'sizes (X0..X8, T0, T4, T8):', per[key])
    # pieces
    dsz = [nt(DX(c, law(m, k))) for m in range(9) for k in CH for c in CH]
    print(f'  D^X_c Law_(m,k) (k in 0,4,8): {sum(dsz)} terms over {len(dsz)} (m,k,c), max {max(dsz)}')
    # (M-b)-style (2,2) T-laws with all nine T_a (no chart substitution), for comparison
    N30 = tuple(f'X{i}' for i in range(9)) + tuple(f'Y{i}' for i in range(9))
    mb = sum(nt(law(m, k).derivative(a)) for m in range(9) for k in range(9) for a in range(9)) + \
        sum(nt(law(m, k).derivative(12 + a)) for m in range(9) for k in range(9) for a in range(9))
    print(f'  (M-b) comparison: the 9x9 (2,2) T-laws 1/2(sum dLaw/dX_a T_a + sum dLaw/dY_a U_a) have {mb} terms in total')
    # spot check of expansion vs structured evaluation
    m, c, cp, L = spot
    Pt, Qt = mc.V_point(rng), mc.V_point(rng)
    pt24 = Pt + Qt
    val = []
    for p in L:
        s = 0
        for e, cf in p.to_dict().items():
            t = md(cf)
            for i, k in enumerate(e):
                if k:
                    t = t * pow(pt24[i], k, P) % P
            s += t
        val.append(s % P)
    print('  spot check expanded == structured:', val == eval_law(m, c, cp, Pt, Qt))
    json.dump(per, open('m2_laws_sizes.json', 'w'))
    print(f'[{time.time() - t0:.0f}s]')
