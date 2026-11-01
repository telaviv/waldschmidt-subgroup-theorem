"""B5 exploration mod p (UNTRUSTED): for F = 6 of the 9 quadrics, dim of ((F):I_A)_3 per mu_10 weight and how
much of it lies outside I_A.  Output: b5_modp.out (one line per subset).
"""
import sys
from jb_common import *

P = 1000003


def md(c):
    return int(c.p) * pow(int(c.q), -1, P) % P


m3 = monos(3)


def ideal_rows(F, e):
    mt = monos(e)
    idx = {m: i for i, m in enumerate(mt)}
    rows = []
    for f in F:
        for sm in monos(e - 2):
            r = [0] * len(mt)
            for k, c in (f * mono(sm)).to_dict().items():
                r[idx[k]] = (r[idx[k]] + md(c)) % P
            rows.append(r)
    return flint.nmod_mat(rows, P), idx


def dualK(F, e):
    M, idx = ideal_rows(F, e)
    K, nul = M.nullspace()   # columns v with M v = 0
    return flint.nmod_mat([[int(K[i, j]) for j in range(nul)] for i in range(K.nrows())], P), idx


def I3_rows(w, Sm):
    gens = [X[k] * Q[i] for k in range(9) for i in range(9) if (WT[k] + weight(Q[i])) % 10 == w] + \
        [C for C in CUB if weight(C) == w]
    sidx = {m: i for i, m in enumerate(Sm)}
    rows = []
    for g in gens:
        r = [0] * len(Sm)
        for k, c in g.to_dict().items():
            r[sidx[k]] = md(c)
        rows.append(r)
    return rows


def colon_info(Fi):
    F = [Q[i] for i in Fi]
    others = [g for g in GENS if not any(g == f for f in F)]
    K = {5: dualK(F, 5), 6: dualK(F, 6)}
    info = {}
    for w in range(10):
        Sm = [e for e in m3 if emono_wt(e) == w]
        blocks = []
        for G in others:
            Kd, idx = K[3 + deg(G)]
            rows = []
            for e in Sm:
                r = [0] * len(idx)
                for k, c in (G * mono(e)).to_dict().items():
                    r[idx[k]] = (r[idx[k]] + md(c)) % P
                rows.append(r)
            blocks.append(flint.nmod_mat(rows, P) * Kd)
        big = [[int(B[a, j]) for B in blocks for j in range(B.ncols())] for a in range(len(Sm))]
        Mt = flint.nmod_mat(big, P).transpose()
        N, nul = Mt.nullspace()
        col = [[int(N[i, j]) for i in range(N.nrows())] for j in range(nul)]
        I3 = I3_rows(w, Sm)
        rI = flint.nmod_mat(I3, P).rank() if I3 else 0
        rA = flint.nmod_mat(I3 + col, P).rank() if (I3 or col) else 0
        if rA > rI:
            info[w] = (len(col), rA - rI)
    return info


if __name__ == '__main__':
    out = open(os.path.join(HERE, 'b5_modp.out'), 'w')
    for Fi in itertools.combinations(range(9), 6):
        inf = colon_info(Fi)
        line = f'{Fi} {inf}'
        print(line, flush=True)
        out.write(line + '\n')
        out.flush()
