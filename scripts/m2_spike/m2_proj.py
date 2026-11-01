"""M2.1 (UNTRUSTED, mod P): (1) degree of the projection (X0:X4:X8): A -> P^2 (HF of I_A + two random linear forms
in X0, X4, X8 stabilises at the degree); (2) HF of J_V + (F) vs the image HF (is I(V) = J_V + (F)?).
"""
import random, flint
import m2_common as mc
from m2_common import P, md, monos, X, T, GV
import jb_common as jb
from m2_hilb import hf_ideal

def hf_unweighted(gens, d, nv):
    rows = monos(d, nv); ridx = {e: i for i, e in enumerate(rows)}
    cols = []
    for g in gens:
        dg = mc.deg(g)
        if dg > d: continue
        gd = {e: md(c) for e, c in g.to_dict().items()}
        for e in monos(d - dg, nv):
            cols.append({tuple(a + b for a, b in zip(e, k)): v for k, v in gd.items()})
    M = flint.nmod_mat(len(rows), len(cols), P)
    for j, col in enumerate(cols):
        for k, v in col.items():
            M[ridx[k], j] = v
    return len(rows) - M.rank()

rng = random.Random(2)
a, b = rng.randrange(1, P), rng.randrange(1, P)
L1 = X[4] - a * X[0]; L2 = X[8] - b * X[0]
print('projection fibre HF (I_A + (X4 - a X0, X8 - b X0)):', [hf_unweighted(mc.GA + [L1, L2], d, 9) for d in range(1, 8)], flush=True)
L1 = X[0] - a * X[4]; L2 = X[8] - b * X[4]
print('  (other affine chart):', [hf_unweighted(mc.GA + [L1, L2], d, 9) for d in range(1, 8)], flush=True)
F = (X[0]*X[2]*X[5] + X[0]*X[1]*X[6] - 2*X[1]*X[3]*X[7] - X[0]*X[7]*X[8] - 2*X[1]*X[3]*T[0]
     + flint.fmpq(1, 2)*X[6]*X[7]*T[0] - X[0]*X[4]*T[4] + X[2]*X[6]*T[4] - X[1]*X[7]*T[4] + X[0]**2*T[8] - 4*X[1]*X[2]*T[8])
print('HF of J_V + (F):', [hf_ideal(GV + [F], d) for d in range(1, 7)], flush=True)
