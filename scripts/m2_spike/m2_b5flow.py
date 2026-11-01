"""M2.1 S3/B5 and the fibre flows (UNTRUSTED; exact over Q unless marked mod P).

B5.  The A-block systems (LSG/Jac/B56: F_i = six quadrics, S_i = cubic, i < 4) give V-systems
     F^V_{i,c} = F_i ++ [the two Pluecker quadrics through chart c], multiplier S_i * X_c  (12 systems, 8 = 12 - 3 - 1
     generators each).  lci_mem reduces to the A-block's lci_mem plus ONE cubic identity (the Wronskian cocycle)
         kappa := X0 P48 - X4 P08 + X8 P04  in  I_A        (T cancels).
     Checked here: kappa in I_A with explicit cofactors; for each (i, c), X_c S_i P_{ll'} in (F^V_{i,c}) (exact
     membership, degree 6, as a cross-check of the reduction); Jacobian rank of F^V_{i,c} = 8 at random points (mod P).
At X = 0: Jacobian rank of all 15 generators at (0; T) (mod P); degree of the projection (X0:X4:X8): A -> P^2.
Flows.  For chart c and j = 1, 2: the T_c-flow  X_c dT_c - T_c dX_c = 1/3 Q_{c,1j}(X)  (K-natural quadrics; for c = 0,
     Q_{0,1j} = 3 X_m X_0), and for l != c the cubic
         R^{(c)}_{jl} = T_c W^{(c)}_{jl}(X) + 1/3 X_l Q_{c,1j}(X) - 1/3 D^{(c)}_j W^{(c)}_{1l}(X)   ( = X_c (X_c dT_l - T_l dX_c) )
     Question: is R^{(c)}_{jl} = X_c * (quadric in X, T) modulo J_V (resp. modulo J_V + (F))?
Usage: python m2_b5flow.py
"""
import json
import os
import pickle
import random
import time

import flint

import m2_common as mc
from m2_common import X, T, CH, GA, GV, PL, P04, P08, P48, member, nterms, emb, monos, mono, md, P
import jb_common as jb

t0 = time.time()
third = flint.fmpq(1, 3)

print('== kappa = X0 P48 - X4 P08 + X8 P04 ==')
kappa = X[0] * P48 - X[4] * P08 + X[8] * P04
print('kappa =', kappa)
cof = member(kappa, GA)
print('kappa in I_A (exact):', cof is not None, ' cofactors:', [str(c) for c in cof] if cof else None)
print('  in (Q)_3 only (no extra cubics):', member(kappa, mc.QA) is not None)

# A-block B5 systems (LSG/Jac/B56: F_i = quadrics {0,1,2,5,6,7}, {2,3,4,6,7,8}, {1,4,5,6,7,8}, {1,2,3,5,6,8})
FS = [(0, 1, 2, 5, 6, 7), (2, 3, 4, 6, 7, 8), (1, 4, 5, 6, 7, 8), (1, 2, 3, 5, 6, 8)]
Sd = pickle.load(open(os.path.join(jb.HERE, 'b5_S.pkl'), 'rb'))
SS = []
for F in FS:
    w, sd = Sd[F]
    SS.append(emb(jb.ctx.from_dict(sd)) if isinstance(sd, dict) else emb(sd))
PLc = {0: (P04, P08, P48), 4: (P04, P48, P08), 8: (P08, P48, P04)}   # (two through c, the third)

print('\n== V-systems: X_c S_i P_third in (F_i, P, P) (exact, degree 6) ==')
for i, F in enumerate(FS):
    for c in CH:
        p1, p2, p3 = PLc[c]
        gens = [mc.QA[j] for j in F] + [p1, p2]
        r = member(X[c] * SS[i] * p3, gens)
        print(f'  system i={i}, chart {c}: {"ok" if r is not None else "FAIL"}'
              f'{"" if r is None else ", cofactor terms " + str(sum(nterms(x) for x in r))}', flush=True)

print('\n== Jacobian rank of the 8 local generators at random points of V (mod P) ==')
rng = random.Random(3)


def jac_rank(gens, pt):
    rows = [[mc.ev(g.derivative(v), pt) for v in range(12)] for g in gens]
    return flint.nmod_mat(rows, P).rank()


for trial in range(2):
    pt = mc.scale(mc.V_point(rng), rng.randrange(1, P))
    for i, F in enumerate(FS):
        for c in CH:
            p1, p2, _ = PLc[c]
            gens = [mc.QA[j] for j in F] + [p1, p2]
            s = mc.ev(SS[i], pt) * pt[c] % P
            print(f'  pt {trial} system ({i},{c}): S_i X_c != 0: {s != 0}, rank = {jac_rank(gens, pt)}', end=';')
    print()
print('  all 15 generators at a random point of V: rank', jac_rank(GV, mc.V_point(rng)))

print('\n== At X = 0 ==')
for trial in range(2):
    pt0 = [0] * 9 + [rng.randrange(P) for _ in range(3)]
    print(f'  Jacobian rank of the 15 generators at (0; T) = {jac_rank(GV, pt0)}  (dim V = 3, codim 8)')
# degree of the projection: I_A + (two generic linear forms in X0, X4, X8), HF in degree 6..8 (mod P)

print('\n== Flows ==')
kq = json.load(open(os.path.join(mc.HERE, 'kleinK.json')))
import sympy as sp  # noqa: E402

Xs = sp.symbols('X0:9')


def kq_poly(c, i, j):
    s = sp.sympify(kq[f'{c},{i},{j}']['Q'], locals={f'X{k}': Xs[k] for k in range(9)})
    p = sp.Poly(sp.expand(s), *Xs)
    d = {}
    for e, cf in p.terms():
        cf = sp.Rational(cf)
        d[tuple(e) + (0, 0, 0)] = flint.fmpq(int(cf.p), int(cf.q))
    return mc.ctx.from_dict(d)


mi = {1: 1, 2: 2}


def Qc(c, j):
    if c == 0:
        return 3 * X[mi[j]] * X[0]
    return kq_poly(c, 1, j)


def Dc(c, j, h):
    """chart-c derivation (direction j) on a polynomial in X"""
    r = mc.ZERO
    for a in range(9):
        wa = emb(mc.wfield(c)[j - 1][a])
        if wa != 0:
            r += wa * h.derivative(a)
    return r


S2 = monos(2)
res = {}
for c in CH:
    for j in (1, 2):
        for l in CH:
            if l == c:
                continue
            Wjl = emb(mc.wfield(c)[j - 1][l])
            W1l = emb(mc.wfield(c)[0][l])
            R = T[c] * Wjl + third * X[l] * Qc(c, j) - third * Dc(c, j, W1l)
            gens = GV + [X[c] * mono(e) for e in S2]
            r = member(R, gens)
            Fpoly = None
            ok = r is not None
            if ok:
                WT = sum((r[len(GV) + k] * mono(e) for k, e in enumerate(S2)), mc.ZERO)
                # cofactors are constants for the X_c * monomial generators
                print(f'  chart {c}, j={j}, l={l}: R = X_c * WT mod J_V with WT = {WT}', flush=True)
                res[f'{c},{j},{l}'] = str(WT)
            else:
                print(f'  chart {c}, j={j}, l={l}: NOT X_c * quadric mod J_V', flush=True)
                res[f'{c},{j},{l}'] = None
json.dump(res, open('m2_flowT.json', 'w'), indent=1)
print(f'[{time.time() - t0:.0f}s]')
