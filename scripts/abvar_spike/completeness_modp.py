"""A0b step 5: completeness of the (2,2) addition laws, and the bidegree of a Nullstellensatz certificate (mod p).

J = (A_k^{(m)} : k, m in S) + I(X) + I(Y) for a set S of laws.  The laws have no common zero on J x J iff
J contains (X)^{e1} (Y)^{e2} for some e1, e2, iff the multiplication map
        (S/I)_{e1-2} (x) (S/I)_{e2-2} (x) span{A_k^{(m)}}  ->  (S/I)_{e1} (x) (S/I)_{e2}
is onto.  We compute its rank mod p.  Normal forms (S/I)_e are computed by evaluation at random points of J(F_p)
(dim 9 e^2 by ideal_P8.py), and the computation is split by the mu_10 weight grading
(wt X = (0,6,4,2,9,7,5,3,8); the laws are weight-homogeneous of weight w_k + w_m + 8 mod 10), which is exact.

A rank equal to the target dimension mod p implies the same over Q (rank can only drop mod p), so "onto mod p" is a
proof of surjectivity over Q, given exact mod-p arithmetic and that the normal-form maps are the true ones (they are:
dim (S/I)_e = 9e^2 is reached by the evaluation matrix, and evaluation factors through S/I).
Usage: python completeness_modp.py p e1 e2 [laws=all|list e.g. 0,3,4]
"""
import itertools
import json
import random
import sys
import time
import numpy as np
import flint
from jac import Fp, X_eval_fn

WT = [0, 6, 4, 2, 9, 7, 5, 3, 8]


def mono_list(e):
    return list(itertools.combinations_with_replacement(range(9), e))


def mono_wt(m):
    return sum(WT[i] for i in m) % 10


def ev_mono(x, m, p):
    r = 1
    for i in m:
        r = r * x[i] % p
    return r


def nf_data(points, e, p):
    """Return (std monomials, dict monomial -> NF row vector (numpy int64 mod p) in the std basis)."""
    monos = mono_list(e)
    n = 9 * e * e if e > 0 else 1
    V = [[ev_mono(x, m, p) for x in points] for m in monos]
    M = flint.nmod_mat(V, p)
    # independent rows greedily: rref of transpose gives pivot columns = independent monomials
    R, rank = M.transpose().rref()
    assert rank == n, (e, rank, n)
    piv = []
    r = 0
    for c in range(len(monos)):
        if r < rank and int(R[r, c]) != 0:
            piv.append(c)
            r += 1
    std = [monos[c] for c in piv]
    # choose n points with invertible V_std
    Vstd = flint.nmod_mat([V[c] for c in piv], p)            # n x N
    R2, rk2 = Vstd.rref()
    pc = []
    r = 0
    for c in range(Vstd.ncols()):
        if r < rk2 and int(R2[r, c]) != 0:
            pc.append(c)
            r += 1
    S = flint.nmod_mat([[V[c][j] for j in pc] for c in piv], p)   # n x n, invertible
    Sinv = S.inv()
    Vall = flint.nmod_mat([[V[i][j] for j in pc] for i in range(len(monos))], p)
    NF = Vall * Sinv            # row i: coordinates of monomial i in the std basis
    NFn = np.array([[int(NF[i, j]) for j in range(n)] for i in range(len(monos))], dtype=np.int64)
    return std, {m: NFn[i] for i, m in enumerate(monos)}


def main():
    p = int(sys.argv[1])
    e1, e2 = int(sys.argv[2]), int(sys.argv[3])
    lawsel = sys.argv[4] if len(sys.argv) > 4 else 'all'
    random.seed(12345)
    F = Fp(p)
    ev = X_eval_fn(p)
    t0 = time.time()
    emax = max(e1, e2)
    pts = []
    while len(pts) < 9 * emax * emax + 40:
        D = F.random_divisor()
        try:
            pts.append(ev(F.mumford_coords(D)))
        except AssertionError:
            pass
    nf = {e: nf_data(pts, e, p) for e in sorted({1, 2, e1 - 2, e2 - 2, e1, e2}) if e >= 0}
    print(f'normal forms done [{time.time() - t0:.1f}s]', flush=True)
    std2, NF2 = nf[2]
    # laws mod p in the std2 (evaluation) basis: 36 x 36 matrices
    lq = json.load(open('laws_Q.json'))
    sel = range(9) if lawsel == 'all' else [int(t) for t in lawsel.split(',')]
    laws = []
    for key, terms in lq['laws'].items():
        k, m = map(int, key.split(','))
        if m not in sel:
            continue
        Amat = np.zeros((36, 36), dtype=np.int64)
        for e, c in terms:
            num, den = (c.split('/') + ['1'])[:2]
            cp = int(num) * pow(int(den), -1, p) % p
            mx = tuple(i for i in range(9) for _ in range(e[i]))
            my = tuple(i for i in range(9) for _ in range(e[9 + i]))
            Amat = (Amat + cp * np.outer(NF2[mx], NF2[my])) % p
        laws.append(((k, m), Amat, (WT[k] + WT[m] + 8) % 10))
    print(f'{len(laws)} law coordinates [{time.time() - t0:.1f}s]', flush=True)

    def mult_tables(e):
        """For alpha in std_{e-2}: matrix N_alpha (36 x n_e) with rows NF_e(alpha * a), a in std2."""
        stde2 = nf[e - 2][0] if e - 2 > 0 else [()]
        NFe = nf[e][1]
        T = {}
        for al in stde2:
            T[al] = np.array([NFe[tuple(sorted(al + a))] for a in std2], dtype=np.int64)
        return T

    T1, T2 = mult_tables(e1), mult_tables(e2)
    std1, std2b = nf[e1][0], nf[e2][0]
    w1 = np.array([mono_wt(m) for m in std1])
    w2 = np.array([mono_wt(m) for m in std2b])
    tw = (w1[:, None] + w2[None, :]) % 10
    n1, n2 = len(std1), len(std2b)
    # per weight class: rows collected as flint matrices incrementally (dense numpy, float-free: int64 mod p)
    blocks = {c: [] for c in range(10)}
    pf = float(p)
    for (k, m), Amat, wl in laws:
        Af = Amat.astype(np.float64)
        for al, Na in T1.items():
            L = (Na.T.astype(np.float64) @ Af) % pf            # n1 x 36
            for be, Nb in T2.items():
                Mv = (L @ Nb.astype(np.float64)) % pf          # n1 x n2
                c = (wl + mono_wt(al) + mono_wt(be)) % 10
                blocks[c].append(Mv[tw == c].astype(np.int64))
    print(f'sources built [{time.time() - t0:.1f}s]', flush=True)
    total_rank = 0
    for c in range(10):
        ncols = int((tw == c).sum())
        rows = blocks[c]
        if not rows:
            continue
        M = flint.nmod_mat([list(map(int, r)) for r in rows], p)
        rk = M.rank()
        total_rank += rk
        print(f'  weight {c}: {len(rows)} sources, target dim {ncols}, rank {rk}', flush=True)
    print(f'(e1,e2)=({e1},{e2}) laws={lawsel}: rank {total_rank} / target {n1 * n2}  '
          f'{"ONTO" if total_rank == n1 * n2 else "not onto"}  [{time.time() - t0:.1f}s]')


if __name__ == '__main__':
    main()
