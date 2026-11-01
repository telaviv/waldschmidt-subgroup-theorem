"""M2.1 S3/B6 (UNTRUSTED generator; exact cofactors over Q): the Noether/Hilbert certificate for J_V.

hilb field (MEB/Block.lean): every monomial of degree hilb_deg lies in (gens) + (y_0, ..., y_g), with y VARIABLES.
For V (g = 3) four variables are needed.  {X = 0} x P^2_T lies in V(J_V), so T0, T4, T8 must all be among the y:
y = (X_a, T0, T4, T8).  Modulo (T) the Pluecker quadrics become 1/3 W-quadrics in X, so the certificate lives in
9 variables:  X_v^{e_v} in I_A + (W_14, W_18, W4_18) + (X_a).
Also: the T = 0 locus V cap {T = 0} = A cap {W_14 = W_18 = W4_18 = 0} (its degree), and the variant with the extra
cubic F (m2_excess.py) added to the generators.
Usage: python m2_b6.py
"""
import time
import m2_common as mc  # sets sys.path for jb_common
import flint
import jb_common as jb
from jb_common import X as X9, member as member9, nterms, monos as monos9, emono_wt, weight as weight9, deg as deg9
from m2_common import P, md
import m2_common as mc

third = flint.fmpq(1, 3)
WQ = [third * jb.W[0][4], third * jb.W[0][8], third * jb.W4[0][8]]
x = X9
Fx = x[0] * x[2] * x[5] + x[0] * x[1] * x[6] - 2 * x[1] * x[3] * x[7] - x[0] * x[7] * x[8]   # F mod T


def hf9(gens, d):
    tot = 0
    G = [(deg9(g), weight9(g), {e: md(c) for e, c in g.to_dict().items()}) for g in gens]
    byw = {}
    for e in monos9(d):
        byw.setdefault(emono_wt(e), []).append(e)
    for w, rows in byw.items():
        ridx = {e: i for i, e in enumerate(rows)}
        cols = []
        for dg, wg, gd in G:
            if dg > d:
                continue
            for e in monos9(d - dg):
                if (emono_wt(e) + wg) % 10 == w:
                    cols.append({tuple(a + b for a, b in zip(e, k)): v for k, v in gd.items()})
        if not cols:
            tot += len(rows); continue
        M = flint.nmod_mat(len(rows), len(cols), P)
        for j, col in enumerate(cols):
            for k, v in col.items():
                M[ridx[k], j] = v
        tot += len(rows) - M.rank()
    return tot


t0 = time.time()
print('Pluecker quadrics mod T (1/3 W):', [str(q) for q in WQ])
print('\n== HF of I_A + (W-quadrics): the scheme V cap {T = 0} ==')
for d in range(1, 7):
    print(f'd={d}: {hf9(jb.GENS + WQ, d)}', flush=True)
print('  with F added:', [hf9(jb.GENS + WQ + [Fx], d) for d in range(1, 8)], flush=True)

print('\n== n0(a) = first degree with S_n in I_A + WQ + (X_a)  [HF mod P = 0; exact direction: HF_Q <= HF_P] ==')
n0 = {}
for a in range(9):
    hs = []
    for d in range(1, 12):
        h = hf9(jb.GENS + WQ + [x[a]], d)
        hs.append(h)
        if h == 0 or (d >= 5 and h == hs[-2]):
            break
    n0[a] = len(hs) if hs[-1] == 0 else None
    print(f'a={a}: HF = {hs}  n0 = {n0[a]}', flush=True)

print('\n== exact e_v (X_v^e in I_A + WQ + (X_a)) and cofactor sizes ==')
best = None
for a in range(9):
    if n0[a] is None:
        continue
    ev_, sizes = [], []
    for v in range(9):
        if v == a:
            ev_.append(1); sizes.append(0); continue
        for e in range(1, 12):
            cof = member9(x[v] ** e, jb.GENS + WQ + [x[a]])
            if cof is not None:
                ev_.append(e); sizes.append(sum(nterms(c) for c in cof)); break
    hd = 1 + sum(e - 1 for e in ev_)
    print(f'a={a}: e = {ev_}, hilb_deg = {hd}, cofactor terms per identity = {sizes}, total = {sum(sizes)}', flush=True)
    if best is None or hd < best[1]:
        best = (a, hd)
print('best:', best, f'[{time.time() - t0:.0f}s]')
