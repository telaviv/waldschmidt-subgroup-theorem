"""B5: choose few local systems (F, S) covering: X_v^{e} in I_A + (S's) for all v (mod p rank tests, UNTRUSTED).
Usage: python b5_pick.py emax
"""
import pickle
import sys
from jb_common import *
from b5_modp import P, md

res = pickle.load(open(os.path.join(HERE, 'b5_S.pkl'), 'rb'))
SS = {Fi: ctx.from_dict(d) for Fi, (w, d) in res.items()}


def in_ideal_modp(T, gens):
    N = deg(T)
    wT = weight(T)
    rows = []
    keys = {}
    for g in gens:
        wg = weight(g)
        for e in monos(N - deg(g)):
            if (emono_wt(e) + wg) % 10 != wT:
                continue
            r = {}
            for k, c in (mono(e) * g).to_dict().items():
                if k not in keys:
                    keys[k] = len(keys)
                r[keys[k]] = md(c)
            rows.append(r)
    for k in T.to_dict():
        if k not in keys:
            keys[k] = len(keys)
    M = flint.nmod_mat(len(rows) + 1, len(keys), P)
    for i, r in enumerate(rows):
        for j, c in r.items():
            M[i, j] = c
    rk = M.rank() if rows else 0
    for k, c in T.to_dict().items():
        M[len(rows), keys[k]] = md(c)
    return M.rank() == rk


def cover_degrees(Fs, emax):
    gens = GENS + [SS[F] for F in Fs]
    out = []
    for v in range(9):
        e = next((e for e in range(3, emax + 1) if in_ideal_modp(X[v] ** e, gens)), None)
        out.append(e)
    return out


if __name__ == '__main__':
    emax = int(sys.argv[1])
    allF = sorted(SS)
    print('all', len(allF), cover_degrees(allF, emax), flush=True)
    # greedy removal keeping the degrees of the full set
    target = cover_degrees(allF, emax)
    cur = allF[:]
    for F in sorted(allF, key=lambda F: -nterms(SS[F])):
        trial = [G for G in cur if G != F]
        if cover_degrees(trial, emax) == target:
            cur = trial
    print('greedy', len(cur), cur, cover_degrees(cur, emax))
    for F in cur:
        print(F, SS[F])
