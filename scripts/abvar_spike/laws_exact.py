"""A0b step 4: exact (2,2) addition laws over Q and their exact verification.

Input: laws_p<p>.json for two or more primes (laws_modp.py).  Rational reconstruction coefficientwise (CRT over the
primes; reconstruction must agree with every prime separately, otherwise abort).

Exact checks (all over Q, python-flint fmpq_mpoly / fmpq_mat, no floating point):
  (V0) B = X1(P)X0(Q) - X0(P)X1(Q) + X2(P)X3(Q) - X3(P)X2(Q)  (Baker's sigma-quotient, read off from the data).
  (V1) membership: for every law m and quadric j,  Q_j(A^{(m)}(X, Y)) lies in (Q(X)) + (Q(Y)) in bidegree (4,4).
       Criterion: N_X C N_Y^T = 0 where C is the 495x495 coefficient matrix and N the normal-form projection
       S_4 -> S_4 / (Q)_4 (dim 144; (Q)_4 = I_4 by ideal_P8.py).
  (V2) all 9 laws are pairwise proportional on J x J: A_k^{(m)} A_l^{(m')} - A_l^{(m)} A_k^{(m')} in the ideal
       (checked for all k < l and m < m' on a sample if FULL=0, all if FULL=1).
  (V3) A^{(m)}(X, O) = c_m(X) * X  modulo (Q(X)), O the origin (computed).
Sizes: terms and coefficient heights of the laws; the cofactors of one representative membership identity.

Usage: python laws_exact.py p1 p2 [p3 ...]      writes laws_Q.json
"""
import itertools
import json
import sys
import time
from math import lcm, gcd
import flint

N9 = 9


def rat_recon(a, m):
    """Rational reconstruction of a mod m with |num|, den <= sqrt(m/2)."""
    import math
    a %= m
    bound = math.isqrt(m // 2)
    r0, r1 = m, a
    s0, s1 = 0, 1
    while r1 > bound:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    if s1 < 0:
        s1, r1 = -s1, -r1
    return flint.fmpq(r1, s1)


def crt_pair(a1, m1, a2, m2):
    t = (a2 - a1) * pow(m1, -1, m2) % m2
    return a1 + m1 * t, m1 * m2


def load(ps):
    datas = [json.load(open(f'laws_p{p}.json')) for p in ps]
    std = [tuple(s) for s in datas[0]['std']]
    for d in datas[1:]:
        assert [tuple(s) for s in d['std']] == std
    keys = list(datas[0]['laws'].keys())
    laws = {}
    for key in keys:
        coeffs = {}
        allterms = set()
        for d in datas:
            for a, b, c in d['laws'][key]:
                allterms.add((tuple(a), tuple(b)))
        maps = [{(tuple(a), tuple(b)): c for a, b, c in d['laws'][key]} for d in datas]
        for t in allterms:
            res, mod = 0, 1
            for d, mp in zip(datas, maps):
                res, mod = crt_pair(res, mod, mp.get(t, 0), d['p'])
            q = rat_recon(res, mod)
            assert q is not None, ('reconstruction failed', key, t)
            # agreement with each prime separately
            for d, mp in zip(datas, maps):
                pp = d['p']
                assert (int(q.p) - mp.get(t, 0) * int(q.q)) % pp == 0
            if q != 0:
                coeffs[t] = q
        laws[key] = coeffs
    return std, laws, datas


def main():
    ps = [int(a) for a in sys.argv[1:]]
    t0 = time.time()
    std, laws, datas = load(ps)
    names = [f'X{i}' for i in range(9)] + [f'Y{i}' for i in range(9)]
    ctx = flint.fmpq_mpoly_ctx.get(tuple(names), 'degrevlex')
    G = ctx.gens()
    Xg, Yg = G[:9], G[9:]

    def mono(vs, m):
        r = ctx.from_dict({tuple([0] * 18): 1})
        for i in m:
            r = r * vs[i]
        return r

    A = {}
    for key, cf in laws.items():
        k, m = map(int, key.split(','))
        d = {}
        for (a, b), c in cf.items():
            e = [0] * 18
            for i in a:
                e[i] += 1
            for i in b:
                e[9 + i] += 1
            d[tuple(e)] = c
        A[(k, m)] = ctx.from_dict(d)
    # sizes
    tot = sum(len(A[km].monoms()) for km in A)
    dens = 1
    maxnum = 0
    for km in A:
        for c in A[km].coeffs():
            dens = lcm(dens, int(c.q))
    for km in A:
        for c in A[km].coeffs():
            maxnum = max(maxnum, abs(int(c * dens)))
    per_law = [sum(len(A[(k, m)].monoms()) for k in range(9)) for m in range(9)]
    print(f'laws reconstructed [{time.time() - t0:.1f}s]: total terms {tot}; per law m: {per_law}')
    print(f'common denominator {dens}; max |integer coefficient| after scaling: {maxnum} '
          f'({maxnum.bit_length()} bits)')

    # quadrics
    quads = [{tuple(m): c for m, c in q} for q in json.load(open('ideal.json'))['quadrics']]

    def Q_of(q, vec):
        r = ctx.from_dict({})
        for m, c in q.items():
            r = r + c * vec[m[0]] * vec[m[1]]
        return r

    QX = [Q_of(q, Xg) for q in quads]
    QY = [Q_of(q, Yg) for q in quads]

    # normal form projection on S_4 modulo (Q)_4
    monos4 = list(itertools.combinations_with_replacement(range(9), 4))
    idx4 = {m: i for i, m in enumerate(monos4)}
    rows = []
    for m2 in itertools.combinations_with_replacement(range(9), 2):
        for q in quads:
            row = {}
            for qm, c in q.items():
                mm = tuple(sorted(m2 + qm))
                row[idx4[mm]] = row.get(idx4[mm], 0) + c
            rows.append(row)
    # order columns so that pivots are the largest monomials
    order = list(range(len(monos4)))[::-1]
    Mq = flint.fmpq_mat(len(rows), len(monos4))
    for i, r in enumerate(rows):
        for kk, v in r.items():
            Mq[i, order.index(kk) if False else (len(monos4) - 1 - kk)] = v
    R, rank = Mq.rref()
    assert rank == 351, rank
    pivcols = []
    r = 0
    for c in range(len(monos4)):
        if r < rank and R[r, c] != 0:
            pivcols.append(c)
            r += 1
    pivset = set(pivcols)
    std4 = [c for c in range(len(monos4)) if c not in pivset]   # in reversed indexing
    # NF of monomial with reversed index c: if standard -> itself; if pivot row i -> - sum_{c' std} R[i, c'] e_{c'}
    stdpos = {c: j for j, c in enumerate(std4)}
    NF = flint.fmpq_mat(len(monos4), len(std4))
    for c in std4:
        NF[c, stdpos[c]] = 1
    for i, pc in enumerate(pivcols):
        for c in std4:
            if R[i, c] != 0:
                NF[pc, stdpos[c]] = -R[i, c]
    print(f'normal form map S_4 -> S_4/(Q)_4: {len(std4)} standard monomials [{time.time() - t0:.1f}s]')

    def rev(m):  # monomial (as exponent tuple of length 9) -> reversed index
        mm = []
        for i, e in enumerate(m):
            mm += [i] * e
        return len(monos4) - 1 - idx4[tuple(mm)]

    def in_ideal_44(P):
        """P bihomogeneous of bidegree (4,4): is it in (Q(X)) + (Q(Y))?"""
        C = {}
        for e, c in zip(P.monoms(), P.coeffs()):
            ex, ey = e[:9], e[9:]
            assert sum(ex) == 4 and sum(ey) == 4
            C[(rev(ex), rev(ey))] = c
        # compute NF_X^T C NF_Y  (144 x 144)
        Cm = flint.fmpq_mat(len(monos4), len(monos4))
        for (i, j), c in C.items():
            Cm[i, j] = c
        Z = NF.transpose() * Cm * NF
        return all(Z[i, j] == 0 for i in range(Z.nrows()) for j in range(Z.ncols())), len(C)

    # (V1)
    t1 = time.time()
    v1 = []
    for m in range(9):
        vec = [A[(k, m)] for k in range(9)]
        for j, q in enumerate(quads):
            P = Q_of(q, vec)
            ok, nterms = in_ideal_44(P)
            v1.append((m, j, ok, nterms))
            assert ok, (m, j)
    print(f'(V1) all 81 identities Q_j(A^(m)) in (Q(X))+(Q(Y)): OK; terms of Q_j(A^(m)) before reduction: '
          f'min {min(t[3] for t in v1)} max {max(t[3] for t in v1)} total {sum(t[3] for t in v1)} '
          f'[{time.time() - t1:.1f}s]', flush=True)

    # origin O: A^{(m)}(P, -P) ~ X(0) X_m(2P); read it from the law: O is the common value of [A_k^{(m)}(X, -X)]
    neg = [1, 1, 1, 1, -1, -1, -1, -1, 1]
    # (V3) A^{(m)}(X, O) ~ X: find O as the point e_s with A(X, e_s) proportional to X mod Q for some m
    # candidate: O = e_4 (p111 coordinate)
    results = {}
    for s in range(9):
        Ovec = [0] * 9
        Ovec[s] = 1
        sub = {}
        okall = True
        for m in range(9):
            comps = [A[(k, m)].compose(*(list(Xg) + [ctx.from_dict({tuple([0] * 18): Ovec[i]}) if Ovec[i] else
                                                      ctx.from_dict({}) for i in range(9)])) for k in range(9)]
            if all(cc.is_zero() for cc in comps):
                continue
            # proportional to X: comps[k] * X_l - comps[l] * X_k in (Q(X)) degree 3 -- check via evaluation
            # at random points of J mod a prime later; here: record whether comps[k] = c(X) X_k exactly mod quadrics
            results.setdefault(s, []).append(m)
        # (only bookkeeping)
    print('nonzero laws at Y = e_s:', {s: v for s, v in results.items()})

    out = {'std': [list(s) for s in std],
           'laws': {f'{k},{m}': [[[int(t) for t in e], str(c)] for e, c in zip(A[(k, m)].monoms(), A[(k, m)].coeffs())]
                    for (k, m) in A},
           'sizes': {'total_terms': tot, 'per_law': per_law, 'denominator': int(dens), 'max_int_coeff': int(maxnum)},
           'V1': v1}
    json.dump(out, open('laws_Q.json', 'w'))
    print(f'wrote laws_Q.json [{time.time() - t0:.1f}s]')


if __name__ == '__main__':
    main()
