"""A0b step 7: sizes of explicit ideal-membership certificates for the law identities (exact over Q).

For a law m and quadric j:  Q_j(A^{(m)}(X,Y)) = sum_i c_i(X,Y) Q_i(X) + sum_i d_i(X,Y) Q_i(Y),
c_i of bidegree (2,4), d_i of bidegree (4,2).  Cofactors by exact linear algebra on the degree-4 Macaulay matrix
of the quadrics ((Q)_4 = I_4, rank 351), solved weight-block by weight-block (so cofactors are weight-homogeneous):
  step X: for each Y-monomial nu, P_nu(X) = NF(P_nu) + sum_i h_{nu,i} Q_i(X);  c_i = sum_nu h_{nu,i} Y^nu
  step Y: the remainder sum_mu X^mu R_mu(Y) has R_mu in I_4(Y); lift likewise -> d_i.
The certificate is then CHECKED exactly (expanding sum c_i Q_i + sum d_i Q_i and comparing).
Also reports: the duplication map Dup = A^{(4)}(X, X) (degree 4) in normal form mod I_4 and unreduced.

Usage: python cert_sizes.py [m j | all]       writes cert_sizes.json; cert_m<m>_j<j>.json for the requested pair
"""
import itertools
import json
import sys
import time
from math import lcm
import flint

WT = [0, 6, 4, 2, 9, 7, 5, 3, 8]
names = [f'X{i}' for i in range(9)] + [f'Y{i}' for i in range(9)]
ctx = flint.fmpq_mpoly_ctx.get(tuple(names), 'degrevlex')
G = ctx.gens()
Xg, Yg = G[:9], G[9:]
monos4 = list(itertools.combinations_with_replacement(range(9), 4))
monos2 = list(itertools.combinations_with_replacement(range(9), 2))
idx4 = {m: i for i, m in enumerate(monos4)}


def exps_to_mono(e):
    return tuple(i for i in range(len(e)) for _ in range(e[i]))


def load():
    quads = [{tuple(m): c for m, c in q} for q in json.load(open('ideal.json'))['quadrics']]
    lq = json.load(open('laws_Q.json'))
    A = {}
    for key, terms in lq['laws'].items():
        k, m = map(int, key.split(','))
        d = {}
        for e, c in terms:
            num, den = (c.split('/') + ['1'])[:2]
            d[tuple(e)] = flint.fmpq(int(num), int(den))
        A[(k, m)] = ctx.from_dict(d)
    return quads, A


def Q_of(q, vec):
    r = ctx.from_dict({})
    for mm, c in q.items():
        r = r + c * vec[mm[0]] * vec[mm[1]]
    return r


class Lifter:
    """Lift elements of I_4 (as vectors over monos4) to sum_{(m2,i)} coeff * m2 * Q_i, weight-blockwise."""

    def __init__(self, quads):
        self.prods = [(m2, i) for m2 in monos2 for i in range(len(quads))]
        rows = []
        for m2, i in self.prods:
            row = {}
            for qm, c in quads[i].items():
                mm = tuple(sorted(m2 + qm))
                row[idx4[mm]] = row.get(idx4[mm], 0) + c
            rows.append(row)
        self.rows = rows
        self.blocks = {}
        wmon = [sum(WT[i] for i in m) % 10 for m in monos4]
        self.wmon = wmon
        for w in range(10):
            cols = [c for c in range(len(monos4)) if wmon[c] == w]
            prs = [r for r in range(len(rows)) if rows[r] and wmon[next(iter(rows[r]))] == w]
            M = flint.fmpq_mat(len(prs), len(cols))
            cidx = {c: j for j, c in enumerate(cols)}
            for a, r in enumerate(prs):
                for c, v in rows[r].items():
                    M[a, cidx[c]] = v
            # choose independent rows (basis of I_4 in this weight) and pivot columns
            R, rk = M.transpose().rref()
            indep = []
            rr = 0
            for c in range(M.nrows()):
                if rr < rk and R[rr, c] != 0:
                    indep.append(c)
                    rr += 1
            Mb = flint.fmpq_mat(len(indep), len(cols))
            for a, r in enumerate(indep):
                for j in range(len(cols)):
                    Mb[a, j] = M[r, j]
            R2, rk2 = Mb.rref()
            pc = []
            rr = 0
            for c in range(len(cols)):
                if rr < rk2 and R2[rr, c] != 0:
                    pc.append(c)
                    rr += 1
            Sq = flint.fmpq_mat(len(indep), len(indep))
            for a in range(len(indep)):
                for b, c in enumerate(pc):
                    Sq[a, b] = Mb[a, c]
            Sinv = Sq.inv()
            # normal form: v -> v - (v[pc] Sinv) Mb   (zero on pc columns)
            self.blocks[w] = dict(cols=cols, cidx=cidx, prs=[prs[r] for r in indep], pc=pc, Sinv=Sinv, Mb=Mb)

    def lift(self, vec):
        """vec: dict col->coeff (degree-4 element). Returns (nf dict, cofactor dict (m2,i)->coeff)."""
        nf, cof = {}, {}
        byw = {}
        for c, v in vec.items():
            byw.setdefault(self.wmon[c], {})[c] = v
        for w, vv in byw.items():
            B = self.blocks[w]
            vp = flint.fmpq_mat(1, len(B['pc']))
            for b, c in enumerate(B['pc']):
                vp[0, b] = vv.get(B['cols'][c], 0)
            coeffs = vp * B['Sinv']
            sub = coeffs * B['Mb']
            for j, c in enumerate(B['cols']):
                r = vv.get(c, 0) - sub[0, j]
                if r != 0:
                    nf[c] = r
            for a, r in enumerate(B['prs']):
                if coeffs[0, a] != 0:
                    cof[self.prods[r]] = coeffs[0, a]
        return nf, cof


def certificate(P, lifter, nquads):
    """Return cofactors c_i, d_i (fmpq_mpoly) with P = sum c_i Q_i(X) + sum d_i Q_i(Y), assuming P in the ideal."""
    # group by Y-monomial
    byY = {}
    for e, c in zip(P.monoms(), P.coeffs()):
        ex, ey = tuple(e[:9]), tuple(e[9:])
        byY.setdefault(ey, {})[idx4[exps_to_mono(ex)]] = c
    cX = [dict() for _ in range(nquads)]
    rem = {}   # (x-col, ey) -> coeff
    for ey, vec in byY.items():
        nf, cof = lifter.lift(vec)
        for (m2, i), v in cof.items():
            e = [0] * 18
            for t in m2:
                e[t] += 1
            for t in range(9):
                e[9 + t] += ey[t]
            cX[i][tuple(e)] = cX[i].get(tuple(e), 0) + v
        for c, v in nf.items():
            rem[(c, ey)] = v
    byX = {}
    for (c, ey), v in rem.items():
        byX.setdefault(c, {})[idx4[exps_to_mono(ey)]] = v
    dY = [dict() for _ in range(nquads)]
    for c, vec in byX.items():
        nf, cof = lifter.lift(vec)
        assert not nf, 'not in the ideal'
        mx = monos4[c]
        for (m2, i), v in cof.items():
            e = [0] * 18
            for t in mx:
                e[t] += 1
            for t in m2:
                e[9 + t] += 1
            dY[i][tuple(e)] = dY[i].get(tuple(e), 0) + v
    return [ctx.from_dict(d) for d in cX], [ctx.from_dict(d) for d in dY]


def main():
    t0 = time.time()
    quads, A = load()
    nq = len(quads)
    lifter = Lifter(quads)
    QX = [Q_of(q, Xg) for q in quads]
    QY = [Q_of(q, Yg) for q in quads]
    print(f'lifter ready [{time.time() - t0:.1f}s]', flush=True)
    which = sys.argv[1:] if len(sys.argv) > 1 else ['all']
    pairs = [(m, j) for m in range(9) for j in range(nq)] if which == ['all'] else [(int(which[0]), int(which[1]))]
    stats = []
    for (m, j) in pairs:
        vec = [A[(k, m)] for k in range(9)]
        P = Q_of(quads[j], vec)
        cX, dY = certificate(P, lifter, nq)
        # exact check
        S = ctx.from_dict({})
        for i in range(nq):
            S = S + cX[i] * QX[i] + dY[i] * QY[i]
        assert (S - P).is_zero(), (m, j)
        nP = len(P.monoms())
        ncof = sum(len(c.monoms()) for c in cX) + sum(len(d.monoms()) for d in dY)
        den = 1
        mx = 0
        for c in cX + dY:
            for v in c.coeffs():
                den = lcm(den, int(v.q))
        for c in cX + dY:
            for v in c.coeffs():
                mx = max(mx, abs(int(v * den)))
        # expanded size of the certificate RHS before cancellation
        nexp = sum(len(c.monoms()) * len(quads[i]) for i, c in enumerate(cX)) + \
            sum(len(d.monoms()) * len(quads[i]) for i, d in enumerate(dY))
        stats.append(dict(m=m, j=j, terms_lhs=nP, cofactor_terms=ncof, expanded_products=nexp,
                          cof_den=int(den), cof_maxbits=int(mx).bit_length()))
        print(f'm={m} j={j}: |Q_j(A)|={nP}, cofactor terms={ncof}, expanded RHS products={nexp}, '
              f'den={den}, max coeff bits={int(mx).bit_length()}  [{time.time() - t0:.1f}s]', flush=True)
        if len(pairs) == 1:
            json.dump({'m': m, 'j': j,
                       'cX': [[[list(map(int, e)), str(c)] for e, c in zip(p.monoms(), p.coeffs())] for p in cX],
                       'dY': [[[list(map(int, e)), str(c)] for e, c in zip(p.monoms(), p.coeffs())] for p in dY]},
                      open(f'cert_m{m}_j{j}.json', 'w'))
    if len(pairs) > 1:
        tot = {k: sum(s[k] for s in stats) for k in ('terms_lhs', 'cofactor_terms', 'expanded_products')}
        print('TOTAL over', len(stats), 'identities:', tot)
        json.dump({'stats': stats, 'total': tot}, open('cert_sizes.json', 'w'), indent=0)
    # duplication
    D = []
    for k in range(9):
        Dk = A[(k, 4)].compose(*(list(Xg) + list(Xg)))
        D.append(Dk)
    nraw = [len(d.monoms()) for d in D]
    print('duplication A^(4)(X,X): terms per coordinate (unreduced, after Y:=X):', nraw, 'total', sum(nraw))


if __name__ == '__main__':
    main()
