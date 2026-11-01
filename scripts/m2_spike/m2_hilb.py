"""M2.1 S3 (UNTRUSTED): Hilbert functions of the (M-a) ideal J_V in P^11, mod p, weight-blocked.

  HF_J(d)   = dim (S/J_V)_d computed mod P (rank of the generator multiples).  Since rank mod P <= rank over Q,
              HF_J over Q <= the printed value [exact direction].
  HF_img(d) = rank of the degree-d monomials evaluated at random points of the image (mod P) [Numerical]; this is
              (for P generic) the Hilbert function of the Zariski closure V.
  Also: the ideals J_V + (y) for B6 candidates y, and J_A + (2 linear forms in X0,X4,X8) (degree of the projection).
Usage: python m2_hilb.py DMAX_J DMAX_IMG  > m2_hilb.out
"""
import json
import sys
import time
import random

import numpy as np
import flint

from m2_common import *


def gdicts(gens):
    out = []
    for g in gens:
        d = {e: md(c) for e, c in g.to_dict().items()}
        out.append((deg(g), weight(g), d))
    return out


def hf_ideal(gens, d, nvars=NV):
    """dim (S/(gens))_d mod P, S = polynomials in the first nvars variables (others must not occur)"""
    G = gdicts(gens)
    tot = 0
    allm = [e for e in monos(d, nvars)]
    byw = {}
    for e in allm:
        byw.setdefault(wt_e(e), []).append(e)
    for w, rows in sorted(byw.items()):
        ridx = {e: i for i, e in enumerate(rows)}
        cols = []
        for (dg, wg, gd) in G:
            if dg > d:
                continue
            for e in monos(d - dg, nvars):
                if (wt_e(e) + wg) % 10 != w:
                    continue
                cols.append({tuple(a + b for a, b in zip(e, k)): v for k, v in gd.items()})
        if not cols:
            tot += len(rows)
            continue
        M = flint.nmod_mat(len(rows), len(cols), P)
        for j, col in enumerate(cols):
            for k, v in col.items():
                M[ridx[k], j] = v
        tot += len(rows) - M.rank()
    return tot


def hf_image(d, pts):
    """rank of degree-d monomials on the given points (numpy, mod P), weight-blocked"""
    A = np.array(pts, dtype=np.int64).T  # NV x npts
    tot = 0
    byw = {}
    for e in monos(d):
        byw.setdefault(wt_e(e), []).append(e)
    for w, rows in sorted(byw.items()):
        vals = []
        for e in rows:
            v = np.ones(A.shape[1], dtype=np.int64)
            for i, k in enumerate(e):
                for _ in range(k):
                    v = v * A[i] % P
            vals.append(v.tolist())
        M = flint.nmod_mat(vals, P)
        tot += M.rank()
    return tot


if __name__ == '__main__':
    DJ = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    DI = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    res = {}
    t0 = time.time()
    print('generators of J_V: 9 quadrics + 3 cubics (I_A) + P04, P08, P48')
    for nm, g in zip(['P04', 'P08', 'P48'], PL):
        print(' ', nm, '=', g)
    print('\n== HF of S/J_V (mod P; an upper bound for the Q-value) vs (d+1)*9d^2 and HF of the image ==')
    rng = random.Random(7)
    npts = 0
    pts = []
    for d in range(1, DJ + 1):
        hj = hf_ideal(GV, d)
        line = f'd={d}: HF_J = {hj}   (d+1)9d^2 = {(d + 1) * 9 * d * d}'
        if d <= DI:
            need = max(len([e for e in monos(d) if wt_e(e) == w]) for w in range(10)) + 50
            while len(pts) < need:
                pts.append(V_point(rng))
            hi = hf_image(d, pts)
            line += f'   HF_img = {hi}   (J excess = {hj - hi})'
            res.setdefault('img', {})[d] = hi
        res.setdefault('J', {})[d] = hj
        print(line, f'  [{time.time() - t0:.0f}s]', flush=True)
    print('\n== HF of S/I_A in 9 variables (check 9d^2) ==')
    for d in range(1, 5):
        print(f'd={d}: {hf_ideal(GA, d, 9)} (9d^2 = {9 * d * d})', flush=True)
    json.dump(res, open('m2_hilb.json', 'w'), indent=1)
