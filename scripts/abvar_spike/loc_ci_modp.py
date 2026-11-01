"""A0c spike: local complete-intersection certificates for the A-block (mod p, sizes only).

For 6 quadrics F = (F_1..F_6) in I_A (random integer combinations of the 9 quadrics) we compute the colon
(F) : I_A in low degree d: forms S of degree d with S * G in (F) for every generator G of I_A (9 quadrics, and the
3 extra cubics of I_3).  Where such an S does not vanish at a point a of J, the 6 forms F generate I_A locally at a
(I_A)_a = (F)_a, so the slice ring is a local complete intersection there.  We report the least d with
((F) : I_A)_d not contained in I_A, and whether a few random choices of F give S's without common zero on J
(tested at random points mod p: [Numerical]).
Usage: python loc_ci_modp.py p dmax ntrials
"""
import itertools
import json
import random
import sys
import flint
from jac import Fp, X_eval_fn


def monos(n, d):
    return list(itertools.combinations_with_replacement(range(n), d))


def poly_mul_mono(poly, m):
    return {tuple(sorted(k + m)): v for k, v in poly.items()}


def to_row(poly, idx, p):
    row = [0] * len(idx)
    for k, v in poly.items():
        row[idx[k]] = (row[idx[k]] + v) % p
    return row


def span_basis(polys, deg, p):
    ms = monos(9, deg)
    idx = {m: i for i, m in enumerate(ms)}
    M = flint.nmod_mat([to_row(q, idx, p) for q in polys], p) if polys else None
    return ms, idx, M


def main():
    p, dmax, ntr = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    random.seed(1)
    quads = [{tuple(m): c for m, c in q} for q in json.load(open('ideal.json'))['quadrics']]
    # I_A in degree 3 by evaluation (includes cubics): kernel of evaluation at points
    F_ = Fp(p)
    ev = X_eval_fn(p)
    pts = []
    while len(pts) < 400:
        D = F_.random_divisor()
        try:
            pts.append(ev(F_.mumford_coords(D)))
        except AssertionError:
            pass

    def ideal_deg(d):
        ms = monos(9, d)
        V = flint.nmod_mat([[eval_m(x, m, p) for x in pts] for m in ms], p)
        # left kernel = I_d
        K = V.transpose().rref()
        return ms, V

    def eval_m(x, m, p):
        r = 1
        for i in m:
            r = r * x[i] % p
        return r

    # cubic generators: a complement of (Q)_3 in I_3; we just use all of I_3 via evaluation
    for trial in range(ntr):
        F = []
        for _ in range(6):
            co = [random.randint(-3, 3) for _ in quads]
            f = {}
            for c, q in zip(co, quads):
                for k, v in q.items():
                    f[k] = f.get(k, 0) + c * v
            F.append({k: v for k, v in f.items() if v})
        found = None
        for d in range(0, dmax + 1):
            # (F)_{d+2}, (F)_{d+3}
            def Fspan(e):
                polys = [poly_mul_mono(f, m) for m in monos(9, e - 2) for f in F]
                ms = monos(9, e)
                idx = {m: i for i, m in enumerate(ms)}
                M = flint.nmod_mat([to_row(q, idx, p) for q in polys], p)
                R, rk = M.rref()
                return ms, idx, R, rk
            ms2, idx2, R2, rk2 = Fspan(d + 2)
            ms3, idx3, R3, rk3 = Fspan(d + 3)
            # generators of I_A: quadrics, and cubics = I_3 basis via evaluation kernel
            ms_3 = monos(9, 3)
            V3 = [[eval_m(x, m, p) for x in pts] for m in ms_3]
            Mv = flint.nmod_mat(V3, p).transpose()        # points x monomials
            Rv, rkv = Mv.rref()
            piv, r = [], 0
            for c in range(len(ms_3)):
                if r < rkv and int(Rv[r, c]) != 0:
                    piv.append(c)
                    r += 1
            free = [c for c in range(len(ms_3)) if c not in piv]
            cubics = []
            for fc in free:
                v = {ms_3[fc]: 1}
                for i, pc in enumerate(piv):
                    if int(Rv[i, fc]):
                        v[ms_3[pc]] = (-int(Rv[i, fc])) % p
                cubics.append(v)
            # unknown S of degree d; condition: S*Q_j in (F)_{d+2}, S*C_j in (F)_{d+3}
            Sm = monos(9, d)
            cols = []
            # build linear map S -> residues; residue modulo row space computed by projecting onto complement
            def residue_map(G, e, ms, idx, R, rk):
                # returns for each S-monomial the vector (S-monomial * G) reduced mod rowspace(R)
                piv, r = [], 0
                for c in range(len(ms)):
                    if r < rk and int(R[r, c]) != 0:
                        piv.append(c)
                        r += 1
                pivset = set(piv)
                out = []
                for sm in Sm:
                    v = [0] * len(ms)
                    for k, c in G.items():
                        kk = tuple(sorted(k + sm))
                        v[idx[kk]] = (v[idx[kk]] + c) % p
                    # reduce
                    for i, pc in enumerate(piv):
                        if v[pc]:
                            f = v[pc]
                            for c2 in range(len(ms)):
                                if int(R[i, c2]):
                                    v[c2] = (v[c2] - f * int(R[i, c2])) % p
                    out.append([v[c] for c in range(len(ms)) if c not in pivset])
                return out
            blocks = []
            for q in quads:
                blocks.append(residue_map(q, d + 2, ms2, idx2, R2, rk2))
            for cb in cubics:
                blocks.append(residue_map(cb, d + 3, ms3, idx3, R3, rk3))
            rows = []
            for si in range(len(Sm)):
                row = []
                for b in blocks:
                    row += b[si]
                rows.append(row)
            M = flint.nmod_mat(rows, p)          # S-coeffs x conditions ; want left kernel
            Kt = M.transpose()
            Rk, rk = Kt.rref()
            dimcolon = len(Sm) - rk
            # dimension of I_A in degree d
            if d >= 2:
                Vd = flint.nmod_mat([[eval_m(x, m, p) for x in pts] for m in Sm], p)
                dimI = len(Sm) - Vd.rank()
            else:
                dimI = 0
            # colon basis (left kernel of M) and whether it vanishes on J
            piv, r = [], 0
            for c in range(Kt.ncols()):
                if r < rk and int(Rk[r, c]) != 0:
                    piv.append(c)
                    r += 1
            free = [c for c in range(Kt.ncols()) if c not in piv]
            outside = 0
            for fc in free:
                v = [0] * len(Sm)
                v[fc] = 1
                for i, pc in enumerate(piv):
                    v[pc] = (-int(Rk[i, fc])) % p
                vals = [sum(v[a] * eval_m(x, Sm[a], p) for a in range(len(Sm))) % p for x in pts[:20]]
                if any(vals):
                    outside += 1
            print(f'trial {trial} d={d}: dim ((F):I_A)_d = {dimcolon}, dim (I_A)_d = {dimI}, '
                  f'colon basis vectors not vanishing on J: {outside}', flush=True)
            if outside:
                found = d
                break
        print(f'trial {trial}: least degree of a colon element outside I_A: {found}', flush=True)


if __name__ == '__main__':
    main()
