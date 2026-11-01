"""B5 exploration (UNTRUSTED): local CI systems F = 6 of the 9 quadrics (sparse), S in ((F) : I_A)_3 outside I_A,
weight-homogeneous (mu_10 grading).  Then the cover degrees e_v with X_v^e in I_A + (S's).
Usage: python b5_explore.py
"""
import pickle
from jb_common import *


def span_mat(polys, keys):
    kidx = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(len(polys), len(keys))
    for r, p in enumerate(polys):
        for e, c in p.to_dict().items():
            M[r, kidx[e]] = c
    return M


m3 = monos(3)


def I3_basis(w):
    return [X[k] * Q[i] for k in range(9) for i in range(9) if (WT[k] + weight(Q[i])) % 10 == w] + \
        [C for C in CUB if weight(C) == w]


def colon3(F):
    """weight-homogeneous S of degree 3 with S*G in (F) for all G in GENS; returns list of (w, [S basis])"""
    out = {}
    others = [g for g in GENS if not any(g == f for f in F)]
    for w in range(10):
        Sm = [e for e in m3 if emono_wt(e) == w]
        unk = [('S', e) for e in Sm]
        for gi, G in enumerate(others):
            dG = deg(G)
            for fi, f in enumerate(F):
                for e in monos(3 + dG - 2):
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
        # outside I_3: rank of Ss + I3 vs I3
        I3 = I3_basis(w)
        rI = span_mat(I3, Sm).rank() if I3 else 0
        if not Ss:
            continue
        rAll = span_mat(I3 + Ss, Sm).rank()
        if rAll > rI:
            # pick representatives outside, reduce modulo I_3 for sparsity
            reps = []
            cur = I3[:]
            for s in Ss:
                if span_mat(cur + [s], Sm).rank() > span_mat(cur, Sm).rank() if cur else True:
                    reps.append(s)
                    cur.append(s)
            out[w] = (rAll - rI, reps)
    return out


if __name__ == '__main__':
    res = {}
    for F_idx in itertools.combinations(range(9), 6):
        F = [Q[i] for i in F_idx]
        c = colon3(F)
        res[F_idx] = c
        print(F_idx, {w: (d, [nterms(s) for s in reps]) for w, (d, reps) in c.items()}, flush=True)
    pickle.dump({k: {w: (d, [s.to_dict() for s in reps]) for w, (d, reps) in v.items()} for k, v in res.items()},
                open(os.path.join(HERE, 'b5_colon.pkl'), 'wb'))
