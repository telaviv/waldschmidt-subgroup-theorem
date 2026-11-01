"""M2.1 spike, common data (UNTRUSTED Python; exact over Q with python-flint, mod-p helpers for ranks).

The (M-a) model of A_sigmabar^natural in P^11, coordinates (X0..X8, T0, T4, T8) = variables 0..8, 9, 10, 11.
  * I_A: the 9 quadrics + 3 cubics of LSG.JacBlock.gensMv (from ../jacblock/jb_common.py);
  * Pluecker quadrics (M2.md 2.2 N2, 2.3):
        P04 = X0 T4 - X4 T0 + 1/3 W_{14}(X)      (chart-0 field W = flowW, flow_W.json)
        P08 = X0 T8 - X8 T0 + 1/3 W_{18}(X)
        P48 = X4 T8 - X8 T4 + 1/3 W4_{18}(X)     (chart-4 field W4C, flow_W4.json)
    On the image T_c = theta_c w - 1/3 d_1 theta_c, these are theta_flow (j = 1) in charts 0 and 4.
Weights: mu_10 weight of T_c = weight of X_c + 3 (d_1 has weight 3): T0 -> 3, T4 -> 2, T8 -> 1.
"""
import itertools
import os
import random
import sys
from fractions import Fraction

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'jacblock'))
import jb_common as jb  # noqa: E402

NV = 12
NAMES12 = tuple(f'X{i}' for i in range(9)) + ('T0', 'T4', 'T8')
ctx = flint.fmpq_mpoly_ctx.get(NAMES12, 'degrevlex')
V = ctx.gens()
X = V[:9]
T = {0: V[9], 4: V[10], 8: V[11]}
TIDX = {0: 9, 4: 10, 8: 11}
ZERO = ctx.from_dict({})
WT12 = jb.WT + [3, 2, 1]
CH = (0, 4, 8)


def emb(p9):
    """embed a 9-variable jb polynomial into the 12-variable ring"""
    return ctx.from_dict({tuple(e) + (0, 0, 0): c for e, c in p9.to_dict().items()}) if p9 != 0 else ZERO


def wfield(c):
    """chart-c flow field (j = 1, 2) as 9-var polys: c = 0 -> flowW, 4 -> W4C, 8 -> W8C"""
    return {0: jb.W, 4: jb.W4, 8: jb.W8}[c]


QA = [emb(q) for q in jb.Q]
CA = [emb(q) for q in jb.CUB]
GA = QA + CA


def pl(c, l, cw=None):
    """X_c T_l - X_l T_c + 1/3 W^{(cw)}_{1l}(X)  (cw = chart whose field is used, default c)"""
    cw = c if cw is None else cw
    return X[c] * T[l] - X[l] * T[c] + flint.fmpq(1, 3) * emb(wfield(cw)[0][l])


P04 = pl(0, 4)
P08 = pl(0, 8)
P48 = pl(4, 8)
PL = [P04, P08, P48]
GV = GA + PL           # the 15 generators of J_V


def deg(p):
    return max(sum(e) for e in p.to_dict()) if p != 0 else -1


def wt_e(e):
    return sum(WT12[i] * e[i] for i in range(NV)) % 10


def weight(p):
    ws = {wt_e(e) for e in p.to_dict()}
    assert len(ws) <= 1, ('not weight-homogeneous', ws)
    return ws.pop() if ws else None


def is_homog(p):
    return len({sum(e) for e in p.to_dict()}) <= 1


_mcache = {}


def monos(d, n=NV):
    key = (d, n)
    if key not in _mcache:
        out = []
        for c in itertools.combinations_with_replacement(range(n), d):
            e = [0] * NV
            for i in c:
                e[i] += 1
            out.append(tuple(e))
        _mcache[key] = out
    return _mcache[key]


def mono(e):
    return ctx.from_dict({tuple(e): 1})


def nterms(p):
    return len(p.to_dict())


def member(Tp, gens, weighted=True, nvars=NV):
    """exact cofactors c_g (homogeneous) with Tp = sum c_g g, or None.  Multipliers range over monomials in the
    first `nvars` variables.  (Copy of jb_common.member for 12 variables.)"""
    if Tp == 0:
        return [ZERO] * len(gens)
    N = deg(Tp)
    assert is_homog(Tp)
    wT = weight(Tp) if weighted else None
    unk = []
    for gi, g in enumerate(gens):
        if g == 0 or deg(g) > N:
            continue
        wg = weight(g) if weighted else None
        for e in monos(N - deg(g), nvars):
            if weighted and (wt_e(e) + wg) % 10 != wT:
                continue
            unk.append((gi, e))
    prods = [mono(e) * gens[gi] for gi, e in unk]
    rows = set(Tp.to_dict().keys())
    for p in prods:
        rows.update(p.to_dict().keys())
    rows = sorted(rows)
    ridx = {r: k for k, r in enumerate(rows)}
    M = flint.fmpq_mat(len(rows), len(unk) + 1)
    for cidx, p in enumerate(prods):
        for e, c in p.to_dict().items():
            M[ridx[e], cidx] = c
    for e, c in Tp.to_dict().items():
        M[ridx[e], len(unk)] = c
    R, rk = M.rref()
    sol = [flint.fmpq(0)] * len(unk)
    for r in range(rk):
        piv = None
        for cc in range(len(unk) + 1):
            if R[r, cc] != 0:
                piv = cc
                break
        if piv == len(unk):
            return None
        sol[piv] = R[r, len(unk)]
    cof = [ZERO] * len(gens)
    for (gi, e), s in zip(unk, sol):
        if s != 0:
            cof[gi] += s * mono(e)
    chk = Tp
    for c, g in zip(cof, gens):
        chk -= c * g
    assert chk == 0
    return cof


# ------------------------------------------------------------------------------------------- mod p helpers
P = 2147483647          # 2^31 - 1, = 3 mod 4


def md(c):
    c = Fraction(int(c.p), int(c.q)) if hasattr(c, 'p') else Fraction(c)
    return c.numerator % P * pow(c.denominator % P, P - 2, P) % P


def ev(p, pt):
    """evaluate a 12-var (or shorter-dict) polynomial at pt (list of residues)"""
    s = 0
    for e, c in p.to_dict().items():
        t = md(c)
        for i, k in enumerate(e):
            if k:
                t = t * pow(pt[i], k, P) % P
        s = (s + t) % P
    return s


def _sqrt(a):
    r = pow(a, (P + 1) // 4, P)
    return r if r * r % P == a % P else None


def curve_pt(rng):
    while True:
        x = rng.randrange(P)
        y = _sqrt((4 * pow(x, 5, P) + 1) % P)
        if y is not None:
            return x, y


def A_point(rng):
    """X(P1 + P2 - 2 inf) in Grant's coordinates, X0 = 1 (model.json formulas), mod P"""
    (x1, y1), (x2, y2) = curve_pt(rng), curve_pt(rng)
    inv = lambda a: pow(a % P, P - 2, P)
    s1 = (x1 + x2) % P
    s2 = x1 * x2 % P
    b1 = (y1 - y2) * inv(x1 - x2) % P
    b0 = (y1 - b1 * x1) % P
    i2, i4 = inv(2), inv(4)
    Xv = [1,
          (b1 * b1 * i4 - s1 ** 3 + s1 * s2) % P,
          (-s2) % P,
          s1,
          (-2 * b0 * s1 * s1 + b0 * s2 - b1 ** 3 * i4 + b1 * s1 ** 3 - 3 * b1 * s1 * s2) % P,
          (-b0 * s1 - b1 * s2) % P,
          b0,
          b1,
          (b0 * b1 * i2 + 2 * s1 * s1 * s2) % P]
    return Xv


def V_point(rng, tau=None):
    """a point of the image of A_sigmabar^natural: X as above, T_c = X_c tau - 1/3 W_{1c}(X)  (chart 0)"""
    Xv = A_point(rng)
    tau = rng.randrange(P) if tau is None else tau
    pt = Xv + [0, 0, 0]
    i3 = pow(3, P - 2, P)
    for c in CH:
        w = ev(emb(jb.W[0][c]), pt) if c != 0 else 0
        pt[TIDX[c]] = (Xv[c] * tau - i3 * w) % P
    return pt


def scale(pt, s):
    return [v * s % P for v in pt]
