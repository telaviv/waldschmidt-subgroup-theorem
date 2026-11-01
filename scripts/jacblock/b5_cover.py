"""B5 cover search (UNTRUSTED).  For each subset F of 6 quadrics, the exact weight-homogeneous S in ((F):I_A)_3
outside I_A (sparse representative modulo I_3 ∩ colon), then the least e_v with X_v^{e_v} in I_A + (chosen S's).
Writes b5_S.pkl: {F: (w, S as dict)}.
Usage: python b5_cover.py
"""
import pickle
import random
from jb_common import *
from b5_modp import P, md, I3_rows

m3 = monos(3)


def exact_colon(Fi, w):
    """exact basis of the weight-w part of ((F):I)_3 (fmpz nullspace), plus the I_3 part."""
    F = [Q[i] for i in Fi]
    others = [g for g in GENS if not any(g == f for f in F)]
    Sm = [e for e in m3 if emono_wt(e) == w]
    unk = [('S', e) for e in Sm]
    for gi, G in enumerate(others):
        for fi, f in enumerate(F):
            for e in monos(3 + deg(G) - 2):
                if (emono_wt(e) + weight(f)) % 10 == (w + weight(G)) % 10:
                    unk.append((gi, fi, e))
    cols = []
    for u in unk:
        if u[0] == 'S':
            cols.append({(gi, ee): c for gi, G in enumerate(others) for ee, c in (mono(u[1]) * G).to_dict().items()})
        else:
            gi, fi, e = u
            cols.append({(gi, ee): -c for ee, c in (mono(e) * F[fi]).to_dict().items()})
    keys = sorted({kk for col in cols for kk in col})
    kidx = {kk: r for r, kk in enumerate(keys)}
    M = flint.fmpz_mat(len(keys), len(unk))
    for ci, col in enumerate(cols):
        for kk, c in col.items():
            M[kidx[kk], ci] = int(c.p)
    N, nul = M.nullspace()
    Ss = []
    for t in range(nul):
        p = ZERO
        for ci, u in enumerate(unk):
            if u[0] == 'S' and N[ci, t] != 0:
                p += int(N[ci, t]) * mono(u[1])
        if p != 0:
            Ss.append(p)
    return Sm, Ss


def sparse_outside(Sm, Ss, w):
    """an element of span(Ss) outside I_3, with few terms: try each basis element and small combos reduced by
    the colon elements lying in I_3."""
    I3 = I3_rows(w, Sm)
    rI = flint.nmod_mat(I3, P).rank() if I3 else 0

    def outside(p):
        v = [md(p.to_dict().get(e, flint.fmpq(0))) if e in p.to_dict() else 0 for e in Sm]
        return flint.nmod_mat(I3 + [v], P).rank() > rI
    # rref of Ss over Q to get sparse combos
    best = None
    Mq = flint.fmpq_mat(len(Ss), len(Sm))
    for r, p in enumerate(Ss):
        for e, c in p.to_dict().items():
            Mq[r, Sm.index(e)] = c
    for trial in range(60):
        order = list(range(len(Sm)))
        if trial:
            random.shuffle(order)
        Mo = flint.fmpq_mat(len(Ss), len(Sm))
        for r in range(len(Ss)):
            for c in range(len(Sm)):
                Mo[r, c] = Mq[r, order[c]]
        R, rk = Mo.rref()
        for r in range(rk):
            p = ZERO
            for c in range(len(Sm)):
                if R[r, c] != 0:
                    p += R[r, c] * mono(Sm[order[c]])
            if outside(p) and (best is None or nterms(p) < nterms(best)):
                best = p
    # clear denominators
    from math import lcm
    den = 1
    for c in best.to_dict().values():
        den = lcm(den, int(c.q))
    return best * den


if __name__ == '__main__':
    random.seed(1)
    lines = open(os.path.join(HERE, 'b5_modp.out')).read().split('\n')
    res = {}
    for ln in lines:
        if not ln.strip():
            continue
        Fi = eval(ln[:ln.index(')') + 1])
        info = eval(ln[ln.index(')') + 2:])
        (w, (_, d)), = info.items()
        Sm, Ss = exact_colon(Fi, w)
        S = sparse_outside(Sm, Ss, w)
        res[Fi] = (w, S.to_dict())
        print(Fi, w, nterms(S), S, flush=True)
    pickle.dump(res, open(os.path.join(HERE, 'b5_S.pkl'), 'wb'))
