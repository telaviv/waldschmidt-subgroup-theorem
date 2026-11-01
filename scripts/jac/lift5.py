"""Degree-d normal form modulo the 9 quadrics (generic d), weight-blocked, with cofactors. UNTRUSTED."""
import itertools, json, os
import flint
HERE = os.path.dirname(os.path.abspath(__file__))
WT = [0, 6, 4, 2, 9, 7, 5, 3, 8]
def load_quads():
    return [{tuple(m): c for m, c in q} for q in json.load(open(os.path.join(HERE, '..', 'abvar_spike', 'ideal.json')))['quadrics']]
class LifterD:
    def __init__(self, quads, d):
        self.d = d
        self.monos = list(itertools.combinations_with_replacement(range(9), d))
        self.idx = {m: i for i, m in enumerate(self.monos)}
        mons2 = list(itertools.combinations_with_replacement(range(9), d - 2))
        self.prods = [(m, i) for m in mons2 for i in range(len(quads))]
        rows = []
        for m, i in self.prods:
            row = {}
            for qm, c in quads[i].items():
                mm = tuple(sorted(m + qm))
                row[self.idx[mm]] = row.get(self.idx[mm], 0) + c
            rows.append(row)
        wmon = [sum(WT[i] for i in m) % 10 for m in self.monos]
        self.wmon = wmon
        self.blocks = {}
        for w in range(10):
            cols = [c for c in range(len(self.monos)) if wmon[c] == w]
            prs = [r for r in range(len(rows)) if rows[r] and wmon[next(iter(rows[r]))] == w]
            if not cols:
                continue
            M = flint.fmpq_mat(len(prs), len(cols))
            cidx = {c: j for j, c in enumerate(cols)}
            for a, r in enumerate(prs):
                for c, v in rows[r].items():
                    M[a, cidx[c]] = v
            R, rk = M.transpose().rref()
            indep, rr = [], 0
            for c in range(M.nrows()):
                if rr < rk and R[rr, c] != 0:
                    indep.append(c); rr += 1
            Mb = flint.fmpq_mat(len(indep), len(cols))
            for a, r in enumerate(indep):
                for j in range(len(cols)):
                    Mb[a, j] = M[r, j]
            R2, rk2 = Mb.rref()
            pc, rr = [], 0
            for c in range(len(cols)):
                if rr < rk2 and R2[rr, c] != 0:
                    pc.append(c); rr += 1
            Sq = flint.fmpq_mat(len(indep), len(indep))
            for a in range(len(indep)):
                for b, c in enumerate(pc):
                    Sq[a, b] = Mb[a, c]
            self.blocks[w] = dict(cols=cols, prs=[prs[r] for r in indep], pc=pc, Sinv=Sq.inv() if len(indep) else None, Mb=Mb)
    def lift(self, vec):
        nf, cof = {}, {}
        byw = {}
        for c, v in vec.items():
            byw.setdefault(self.wmon[c], {})[c] = v
        for w, vv in byw.items():
            B = self.blocks[w]
            if not B['pc']:
                nf.update(vv); continue
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
if __name__ == '__main__':
    import sys, time
    from math import lcm
    d = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    t = time.time()
    L = LifterD(load_quads(), d)
    den, maxlen, std, ncof, maxl1 = 1, 0, set(), 0, 0
    rows = {}
    for c in range(len(L.monos)):
        nf, cof = L.lift({c: flint.fmpq(1)})
        rows[c] = nf
        std |= set(nf)
        maxlen = max(maxlen, len(nf)); ncof += len(cof)
        for v in list(nf.values()) + list(cof.values()):
            den = lcm(den, int(v.q))
    print(f'd={d}: monomials {len(L.monos)}, std {len(std)}, max row length {maxlen}, lcm den {den}, cofactor terms {ncof}, {time.time()-t:.1f}s')
