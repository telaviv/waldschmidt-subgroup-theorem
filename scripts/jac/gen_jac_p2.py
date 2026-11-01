"""Stage A1, P2 (`dup_ne_zero`): an exact degree-7 Nullstellensatz certificate (UNTRUSTED generator).

For each i:  D * X_i^7 = sum_k C_ik(X) dup_k(X) + sum_j H_ij(X) Q_j(X)   as polynomials (exact),
with dup_k(X) = 32 A_k^(4)(X, X) (the data), C_ik of degree 3, H_ij of degree 5, integer coefficients.
Writes scripts/jac/p2_cert.json (C, H, D).  Usage: python scripts/jac/gen_jac_p2.py
"""
import itertools, json, os, sys, time
from fractions import Fraction
from math import lcm
import flint
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import slots
from lift5 import LifterD, load_quads, WT

def mono_of_code(c):
    return tuple(i for i in range(9) for _ in range(c // 8 ** i % 8))

def main():
    t0 = time.time()
    quads = load_quads()
    laws = slots.load_laws()
    L7 = LifterD(quads, 7)
    print(f'LifterD(7) ready [{time.time() - t0:.0f}s]', flush=True)
    # dup_k as dict mono(deg 4) -> int
    dup = []
    for k in range(9):
        d = {}
        for a, r in laws[(k, 4)]:
            for b, c, s in r:
                m = tuple(sorted(mono_of_code(a) + mono_of_code(b)))
                d[m] = d.get(m, 0) + (-c if s else c)
        dup.append({m: v for m, v in d.items() if v})
    mons3 = list(itertools.combinations_with_replacement(range(9), 3))
    def vec7(poly):
        return {L7.idx[m]: flint.fmpq(v) for m, v in poly.items() if v}
    # normal forms of dup_k * m3 and X_i^7
    cols = []        # (k, m3) -> nf dict
    for k in range(9):
        for m in mons3:
            prod = {}
            for mm, v in dup[k].items():
                key = tuple(sorted(mm + m))
                prod[key] = prod.get(key, 0) + v
            nf, _ = L7.lift(vec7(prod))
            cols.append(((k, m), nf))
    print(f'normal forms of dup_k * m3 [{time.time() - t0:.0f}s]', flush=True)
    stdset = sorted({c for _, nf in cols for c in nf})
    out = {'C': {}, 'H': {}, 'D': {}}
    for i in range(9):
        target = {tuple([i] * 7): 1}
        nfT, _ = L7.lift(vec7(target))
        # solve sum_c x_c nf_c = nfT over Q, weight-restricted: only columns of the right weight
        w = (7 * WT[i]) % 10
        use = [(key, nf) for key, nf in cols if nf and L7.wmon[next(iter(nf))] == w]
        rowsidx = sorted({c for _, nf in use for c in nf} | set(nfT))
        ridx = {c: r for r, c in enumerate(rowsidx)}
        M = flint.fmpq_mat(len(rowsidx), len(use) + 1)
        for j, (key, nf) in enumerate(use):
            for c, v in nf.items():
                M[ridx[c], j] = v
        for c, v in nfT.items():
            M[ridx[c], len(use)] = v
        R, rk = M.rref()
        piv = []
        r = 0
        for c in range(len(use) + 1):
            if r < rk and R[r, c] != 0:
                piv.append(c); r += 1
        assert len(use) not in piv, f'X_{i}^7 not in (dup) + I'
        sol = {}
        for r, c in enumerate(piv):
            sol[use[c][0]] = R[r, len(use)]
        # C_ik and the remainder in (Q)_7
        Cpoly = {}
        resid = {tuple([i] * 7): flint.fmpq(1)}
        for (k, m), v in sol.items():
            if v == 0:
                continue
            Cpoly[(k, m)] = v
            for mm, dv in dup[k].items():
                key = tuple(sorted(mm + m))
                resid[key] = resid.get(key, flint.fmpq(0)) - v * dv
        nfR, cof = L7.lift({L7.idx[m]: v for m, v in resid.items() if v != 0})
        assert not nfR, 'residual not in (Q)_7'
        # integer scaling
        D = 1
        for v in list(Cpoly.values()) + list(cof.values()):
            D = lcm(D, int(v.q))
        out['D'][i] = D
        out['C'][i] = [[k, list(m), str(int((v * D).p))] for (k, m), v in Cpoly.items()]
        # cof: (m5, j) -> coeff ;  resid = sum cof * m5 * Q_j  => D X^7 = sum (D C) dup + sum (D cof m5) Q_j
        out['H'][i] = [[j, list(m5), str(int((v * D).p))] for (m5, j), v in cof.items()]
        print(f'i={i}: |C| = {len(Cpoly)}, |H| = {len(cof)}, D = {D} [{time.time() - t0:.0f}s]', flush=True)
    json.dump(out, open(os.path.join(HERE, 'p2_cert.json'), 'w'))

if __name__ == '__main__':
    main()
