"""Find I_3 = {C in S_3 : X_k C in (Q)_4 for all k} and three cubics spanning I_3/(Q)_3 (UNTRUSTED)."""
from jb_common import *

def span_rows(polys, keys):
    kidx = {k: i for i, k in enumerate(keys)}
    M = flint.fmpq_mat(len(polys), len(keys))
    for r, p in enumerate(polys):
        for e, c in p.to_dict().items():
            M[r, kidx[e]] = c
    return M

m3 = monos(3)
extras = []
for w in range(10):
    Cm = [e for e in m3 if emono_wt(e) == w]
    if not Cm:
        continue
    # unknowns: C coeffs, then per k cofactors (m2 * Q_i) with weight matching
    unk = [('C', e) for e in Cm]
    for k in range(9):
        for i in range(9):
            for e in monos(2):
                if (emono_wt(e) + weight(Q[i])) % 10 == (w + WT[k]) % 10:
                    unk.append((k, i, e))
    eqs = {}
    cols = []
    for u in unk:
        if u[0] == 'C':
            cols.append({(k, ee): c for k in range(9) for ee, c in (X[k] * mono(u[1])).to_dict().items()})
        else:
            k, i, e = u
            cols.append({(k, ee): -c for ee, c in (mono(e) * Q[i]).to_dict().items()})
    keys = sorted({kk for col in cols for kk in col})
    kidx = {kk: r for r, kk in enumerate(keys)}
    M = flint.fmpz_mat(len(keys), len(unk))
    for ci, col in enumerate(cols):
        for kk, c in col.items():
            M[kidx[kk], ci] = int(c.p)
    # nullspace, project to C part
    N, nul = M.nullspace()
    Cs = []
    for t in range(nul):
        p = ZERO
        for ci, u in enumerate(unk):
            if u[0] == 'C' and N[ci, t] != 0:
                p += N[ci, t] * mono(u[1])
        Cs.append(p)
    # rank of C part, and of (Q)_3 in this weight
    Q3 = [X[k] * Q[i] for k in range(9) for i in range(9) if (WT[k] + weight(Q[i])) % 10 == w]
    rI = span_rows(Cs, Cm).rank() if Cs else 0
    rQ = span_rows(Q3, Cm).rank() if Q3 else 0
    print('weight', w, 'dim I3', rI, 'dim (Q)3', rQ)
    if rI > rQ:
        # pick elements of Cs not in span Q3, try to find a sparse rep: reduce by Q3 rows via rref of [Q3; C]
        for C in Cs:
            if span_rows(Q3 + [C], Cm).rank() > rQ:
                # reduce C modulo Q3: minimize support greedily via rref with C last
                M2 = span_rows(Q3 + [C], Cm)
                # put C's reduced form: solve least support by rref on transposed order
                extras.append((w, C))
                break
for w, C in extras:
    print(w, C)

print('--- reduced reps')
import random
best = {}
for w, C in extras:
    Cm = [e for e in m3 if emono_wt(e) == w]
    Q3 = [X[k] * Q[i] for k in range(9) for i in range(9) if (WT[k] + weight(Q[i])) % 10 == w]
    for trial in range(200):
        order = Cm[:]
        if trial:
            random.shuffle(order)
        M = span_rows(Q3, order)
        R, rk = M.rref()
        piv = []
        for r in range(rk):
            for cc in range(len(order)):
                if R[r, cc] != 0:
                    piv.append((r, cc)); break
        vec = [C.to_dict().get(e, 0) for e in order]
        vec = [flint.fmpq(int(v.p), int(v.q)) if not isinstance(v, int) else flint.fmpq(v) for v in vec]
        for r, cc in piv:
            f = vec[cc]
            if f != 0:
                for c2 in range(len(order)):
                    vec[c2] -= f * R[r, c2]
        p = ZERO
        for e, v in zip(order, vec):
            if v != 0:
                p += v * mono(e)
        if w not in best or nterms(p) < nterms(best[w]):
            best[w] = p
    print(w, nterms(best[w]), best[w])
