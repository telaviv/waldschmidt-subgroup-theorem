"""M2.1 B6 with a linear form (UNTRUSTED; HF mod P, cofactors exact over Q).

m2_b6.out: NO single variable X_a works as the fourth y (each X_a vanishes on part of the degree-54 scheme
Z = V cap {T0 = T4 = T8 = 0}; the origin e4 is in Z, so the form must contain X4).
So y = (T0, T4, T8, l) with l = X4 + lam X_b.  Modulo (T, l) we substitute X4 = -lam X_b (a ring map, exact modulo
(l)): the certificate lives in 8 variables:  X_v^{e_v} in sub(I_A + WQ),  v != 4.
Lean form: M == sub(M) mod (l); every monomial of sub(M) of degree >= 1 + sum (e_v - 1) is in sub(I_A + WQ) by
pigeonhole; sub(G) == G mod (l).
Usage: python m2_b6lin.py
"""
import itertools
import time

import flint

import m2_common as mc  # noqa: F401  (sets sys.path)
from m2_common import P, md
import jb_common as jb
from jb_common import X as x, nterms

third = flint.fmpq(1, 3)
WQ = [third * jb.W[0][4], third * jb.W[0][8], third * jb.W4[0][8]]
GZ = jb.GENS + WQ
VARS8 = [v for v in range(9) if v != 4]


def sub(p, b, lam):
    """X4 -> -lam X_b"""
    return p.compose(*[x[i] if i != 4 else -lam * x[b] for i in range(9)])


_mc = {}


def monos8(d):
    if d not in _mc:
        out = []
        for c in itertools.combinations_with_replacement(VARS8, d):
            e = [0] * 9
            for i in c:
                e[i] += 1
            out.append(tuple(e))
        _mc[d] = out
    return _mc[d]


def mat_of(gens, d):
    rows = monos8(d)
    ridx = {e: i for i, e in enumerate(rows)}
    unk, cols = [], []
    for gi, g in enumerate(gens):
        dg = jb.deg(g)
        if g == 0 or dg > d:
            continue
        gd = g.to_dict()
        for e in monos8(d - dg):
            unk.append((gi, e))
            cols.append({tuple(a + bb for a, bb in zip(e, k)): v for k, v in gd.items()})
    return rows, ridx, unk, cols


def nmat(rows, ridx, cols, extra=None):
    M = flint.nmod_mat(len(rows), len(cols) + (1 if extra is not None else 0), P)
    for j, col in enumerate(cols):
        for k, v in col.items():
            M[ridx[k], j] = md(v)
    if extra is not None:
        for k, v in extra.to_dict().items():
            M[ridx[k], len(cols)] = md(v)
    return M


def hf8(gens, d):
    rows, ridx, unk, cols = mat_of(gens, d)
    return len(rows) - nmat(rows, ridx, cols).rank()


def member8(Tp, gens):
    """exact cofactors (fmpq, on a mod-P pivot column basis) or None"""
    d = jb.deg(Tp)
    rows, ridx, unk, cols = mat_of(gens, d)
    Mq = nmat(rows, ridx, cols)
    rk = Mq.rank()
    if nmat(rows, ridx, cols, Tp).rank() != rk:
        return None
    R, rk = Mq.rref()
    piv, r = [], 0
    for c in range(len(cols)):
        if r < rk and R[r, c] != 0:
            piv.append(c)
            r += 1
    A = flint.fmpq_mat(len(rows), len(piv) + 1)
    for jj, c in enumerate(piv):
        for k, v in cols[c].items():
            A[ridx[k], jj] = v
    for k, v in Tp.to_dict().items():
        A[ridx[k], len(piv)] = v
    RR, rr = A.rref()
    sol = [flint.fmpq(0)] * len(piv)
    for i in range(rr):
        pc = next(c for c in range(len(piv) + 1) if RR[i, c] != 0)
        if pc == len(piv):
            return None
        sol[pc] = RR[i, len(piv)]
    cof = [jb.ZERO] * len(gens)
    for jj, c in enumerate(piv):
        if sol[jj] != 0:
            gi, e = unk[c]
            cof[gi] += sol[jj] * jb.mono(e)
    chk = Tp
    for cc, g in zip(cof, gens):
        chk -= cc * g
    assert chk == 0
    return cof


if __name__ == '__main__':
    t0 = time.time()
    good = []
    for b in VARS8:
        for lam in (1, -1, 2):
            G8 = [sub(g, b, lam) for g in GZ]
            h = hf8(G8, 6)
            print(f'l = X4 + ({lam}) X{b}: HF_6 = {h}', flush=True)
            if h == 0:
                good.append((b, lam))
                break
    print('good:', good, f'[{time.time() - t0:.0f}s]', flush=True)
    best = None
    for b, lam in good:
        G8 = [sub(g, b, lam) for g in GZ]
        ev, sz = [], []
        for v in VARS8:
            for e in range(1, 10):
                cof = member8(x[v] ** e, G8)
                if cof is not None:
                    ev.append(e)
                    sz.append(sum(nterms(c) for c in cof))
                    break
        hd = 1 + sum(e - 1 for e in ev)
        print(f'l = X4 + ({lam}) X{b}: e_v (v = {VARS8}) = {ev}, hilb_deg = {hd}, exact cofactor terms {sz}'
              f' (total {sum(sz)}) [{time.time() - t0:.0f}s]', flush=True)
        if best is None or hd < best[2]:
            best = (b, lam, hd)
    print('best:', best)
