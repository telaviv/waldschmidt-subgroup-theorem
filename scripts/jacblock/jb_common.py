"""Common data for the A4/gamma certificate generators (UNTRUSTED; every output is re-checked in Lean).

Polynomials in X0..X8 over Q are flint fmpq_mpoly.  Data:
  Q[0..8]      the 9 quadrics (ideal.json, = LSG.Jac.quad)
  W, W4, W8    the chart-0/4/8 flow quadratics exactly as in Lean:
               flowW j = Wn/2 (flow_W.json), W4C j = W4n/4 (flow_W4.json), W8C j = W8n/4 (flow_W8.json)
  CUB[0..2]    three cubics spanning I_3 / (Q)_3 (chosen in find_cubics, fixed below once found)
Helpers: weight (mu_10 grading), ideal membership by exact linear algebra (weight-blocked), Lean printing.
"""
import itertools
import json
import os
from fractions import Fraction

import flint

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, '..', '..'))
JAC = os.path.join(HERE, '..', 'jac')
SPIKE = os.path.join(HERE, '..', 'abvar_spike')

NAMES = tuple(f'X{i}' for i in range(9))
ctx = flint.fmpq_mpoly_ctx.get(NAMES, 'degrevlex')
X = ctx.gens()
ZERO = ctx.from_dict({})
ONE = ctx.from_dict({(0,) * 9: 1})
WT = [0, 6, 4, 2, 9, 7, 5, 3, 8]


def const(c):
    return ctx.from_dict({(0,) * 9: c}) if c != 0 else ZERO


def q(c):
    c = Fraction(c)
    return flint.fmpq(c.numerator, c.denominator)


def _load_quads():
    qs = json.load(open(os.path.join(SPIKE, 'ideal.json')))['quadrics']
    out = []
    for qq in qs:
        p = ZERO
        for (a, b), c in qq:
            p += c * X[a] * X[b]
        out.append(p)
    return out


Q = _load_quads()


def _load_field(fn, scale=1):
    d = json.load(open(os.path.join(JAC, fn)))
    F = [[ZERO] * 9 for _ in range(2)]
    for k, v in d.items():
        j, i = map(int, k.split(','))
        p = ZERO
        for (a, b), c in v:
            p += q(Fraction(c) * scale) * X[a] * X[b]
        F[j - 1][i] = p
    return F


W = _load_field('flow_W.json')      # flowW j i  (i = 0 entry is 0)
W4 = _load_field('flow_W4.json')    # W4C j i    (i = 4 entry is 0)
W8 = _load_field('flow_W8.json')    # W8C j i    (i = 8 entry is 0)


def deg(p):
    return max(sum(e) for e in p.to_dict()) if p != 0 else -1


def weight(p):
    ws = {sum(WT[i] * e[i] for i in range(9)) % 10 for e in p.to_dict()}
    assert len(ws) <= 1, ('not weight-homogeneous', ws)
    return ws.pop() if ws else None


def is_homog(p):
    return len({sum(e) for e in p.to_dict()}) <= 1


def monos(d):
    """exponent tuples of degree d"""
    out = []
    for c in itertools.combinations_with_replacement(range(9), d):
        e = [0] * 9
        for i in c:
            e[i] += 1
        out.append(tuple(e))
    return out


def mono(e):
    return ctx.from_dict({tuple(e): 1})


def emono_wt(e):
    return sum(WT[i] * e[i] for i in range(9)) % 10


def deriv(p, i):
    return p.derivative(i)


def D(F, j, h):
    """formal derivation sum_i F[j][i] d_i h"""
    r = ZERO
    for i in range(9):
        if F[j][i] != 0:
            r += F[j][i] * h.derivative(i)
    return r


def Dv(F, v, h):
    r = ZERO
    for i in range(9):
        fi = v[0] * F[0][i] + v[1] * F[1][i]
        if fi != 0:
            r += fi * h.derivative(i)
    return r


def member(T, gens, weighted=True):
    """Find cofactors c_g (homogeneous) with T = sum c_g g.  gens: list of homogeneous polys.
    Uses the mu_10 weight grading if all inputs are weight-homogeneous.  Returns list of cofactors or None."""
    if T == 0:
        return [ZERO] * len(gens)
    N = deg(T)
    assert is_homog(T)
    wT = weight(T) if weighted else None
    unk = []  # (gen index, exponent)
    for gi, g in enumerate(gens):
        dg = deg(g)
        if g == 0 or dg > N:
            continue
        wg = weight(g) if weighted else None
        for e in monos(N - dg):
            if weighted and (emono_wt(e) + wg) % 10 != wT:
                continue
            unk.append((gi, e))
    prods = [mono(e) * gens[gi] for gi, e in unk]
    rowsset = set()
    for p in prods:
        rowsset.update(p.to_dict().keys())
    rowsset.update(T.to_dict().keys())
    rows = sorted(rowsset)
    ridx = {r: k for k, r in enumerate(rows)}
    M = flint.fmpq_mat(len(rows), len(unk) + 1)
    for cidx, p in enumerate(prods):
        for e, c in p.to_dict().items():
            M[ridx[e], cidx] = c
    for e, c in T.to_dict().items():
        M[ridx[e], len(unk)] = c
    R, rk = M.rref()
    # read off a particular solution (free vars = 0)
    sol = [flint.fmpq(0)] * len(unk)
    for r in range(rk):
        piv = None
        for cc in range(len(unk) + 1):
            if R[r, cc] != 0:
                piv = cc
                break
        if piv == len(unk):
            return None  # inconsistent
        sol[piv] = R[r, len(unk)]
    cof = [ZERO] * len(gens)
    for (gi, e), s in zip(unk, sol):
        if s != 0:
            cof[gi] += s * mono(e)
    chk = T
    for c, g in zip(cof, gens):
        chk -= c * g
    assert chk == 0
    return cof


def lean_poly(p, v='X', ring_cast=''):
    """Lean expression of p in variables `v i` (rational coefficients written as (a/b))."""
    if p == 0:
        return '0'
    terms = []
    for e, c in sorted(p.to_dict().items(), reverse=True):
        c = Fraction(int(c.p), int(c.q))
        fac = []
        for i in range(9):
            if e[i] == 1:
                fac.append(f'{v} {i}')
            elif e[i] > 1:
                fac.append(f'{v} {i} ^ {e[i]}')
        mon = ' * '.join(fac)
        a = abs(c)
        cs = (str(a.numerator) if a.denominator == 1 else f'({a.numerator} / {a.denominator})')
        if mon:
            t = mon if a == 1 else f'{cs} * {mon}'
        else:
            t = cs
        terms.append(('-' if c < 0 else '+', t))
    s = ('-' if terms[0][0] == '-' else '') + terms[0][1]
    for sg, t in terms[1:]:
        s += f' {sg} {t}'
    return s


def nterms(p):
    return len(p.to_dict())


# The three extra cubics (find_cubics.py: I_3 = (Q)_3 + span(CUB), dims 84 = 81 + 3; weights 0, 2, 8).
CUB = [4 * X[0] * X[1] * X[2] + 4 * X[1] * X[3] ** 2 - X[0] * X[5] * X[7] + 2 * X[0] * X[3] * X[8],
       2 * X[2] ** 3 - X[0] ** 2 * X[3] + 2 * X[1] * X[2] * X[3] - X[0] * X[5] * X[6],
       4 * X[2] * X[3] ** 2 - X[0] * X[6] * X[7] + 2 * X[0] ** 2 * X[8]]
GENS = Q + CUB
