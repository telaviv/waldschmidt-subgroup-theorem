"""A0b step 3 (mod p): the 9 addition laws of bidegree (2,2) on Grant's P^8 model, by interpolation over F_p.

Theory (Lange-Ruppert; for L = 3*Theta symmetric): the (2,2) laws modulo (I(X), I(Y)) form a 9-dimensional space
~ H^0(J x J, d^*L) = H^0(J, L), d(x, y) = x - y.  The law attached to the section X_m is, in affine normalisation
(X_0(P) = X_0(Q) = 1),
        A_k^{(m)}(P, Q) = X_k(P + Q) * X_m(P - Q) * B(P, Q)^3,
with B the bidegree-(1,1) form whose divisor on J x J is m^*Theta + d^*Theta (genus-2 analogue of
sigma(u+v)sigma(u-v)/sigma(u)^2 sigma(v)^2 = p11(u) - p11(v) + ...; Baker).  B is determined here, up to a scalar, by
linear algebra (vanishing on {Q = P + T} and {Q = -P + T}, T in Theta), not assumed.

Representation: each A_k^{(m)} is written with standard monomials only (36 per side, a complement of span(quadrics)
in S_2), so it is unique; 1296 unknowns per (k, m).

Usage: python laws_modp.py p [npairs]    -> writes laws_p<p>.json  (B and all 81 A_k^{(m)} mod p)
"""
import itertools
import json
import random
import sys
import time
import flint
from jac import Fp, X_eval_fn


def load_quadrics():
    with open('ideal.json') as fh:
        d = json.load(fh)
    return [{tuple(m): c for m, c in q} for q in d['quadrics']]


def standard_monomials(quads):
    """Complement of span(quadrics) in S_2: eliminate pivots in the order given by monos (reversed, so the pivots are
    the lexicographically largest monomials), return (standard list, reduction map pivot -> combination)."""
    monos = list(itertools.combinations_with_replacement(range(9), 2))
    order = list(reversed(monos))      # pivot preference: largest first
    idx = {m: i for i, m in enumerate(order)}
    M = flint.fmpq_mat(len(quads), len(order))
    for i, q in enumerate(quads):
        for m, c in q.items():
            M[i, idx[m]] = c
    R, rank = M.rref()
    pivots = []
    r = 0
    for c in range(len(order)):
        if r < rank and R[r, c] != 0:
            pivots.append(c)
            r += 1
    std = [order[c] for c in range(len(order)) if c not in pivots]
    # pivot monomial = - sum R[i, c] * order[c] (non-pivot c)
    red = {}
    for i, pc in enumerate(pivots):
        red[order[pc]] = {order[c]: -R[i, c] for c in range(len(order)) if c != pc and R[i, c] != 0}
    return sorted(std), red


def mono_val(v, m, p):
    r = 1
    for i in m:
        r = r * v[i] % p
    return r


def main():
    p = int(sys.argv[1])
    npairs = int(sys.argv[2]) if len(sys.argv) > 2 else 1400
    random.seed(p)
    F = Fp(p)
    ev = X_eval_fn(p)
    quads = load_quadrics()
    std, red = standard_monomials(quads)
    assert len(std) == 36
    t0 = time.time()

    def Xof(D):
        return ev(F.mumford_coords(D))

    # ---- B: bidegree (1,1), 81 unknowns, vanishing on {(P, P+T)} and {(P, -P+T)}
    rows = []
    while len(rows) < 200:
        P = F.random_divisor()
        T = F.random_theta_point()
        for Q in (F.add(P, T), F.add(F.neg(P), T)):
            try:
                xp, xq = Xof(P), Xof(Q)
            except AssertionError:
                continue
            rows.append([xp[i] * xq[j] % p for i in range(9) for j in range(9)])
    M = flint.nmod_mat(rows, p)
    R, rank = M.rref()
    nullity = 81 - rank
    print('B: rank', rank, 'nullity', nullity, flush=True)
    assert nullity == 1
    # kernel vector
    piv = []
    r = 0
    for c in range(81):
        if r < rank and int(R[r, c]) != 0:
            piv.append(c)
            r += 1
    free = [c for c in range(81) if c not in piv][0]
    Bv = [0] * 81
    Bv[free] = 1
    for i, pc in enumerate(piv):
        Bv[pc] = (-int(R[i, free])) % p
    # normalise: make the coefficient of X1(P)X0(Q) equal to 1 if nonzero, else first nonzero
    k0 = 1 * 9 + 0 if Bv[9] else next(i for i in range(81) if Bv[i])
    inv = pow(Bv[k0], -1, p)
    Bv = [x * inv % p for x in Bv]

    def Bval(xp, xq):
        return sum(Bv[i * 9 + j] * xp[i] * xq[j] for i in range(9) for j in range(9)) % p

    # ---- laws: 1296 unknowns, 81 right-hand sides
    basis = [(a, b) for a in std for b in std]
    rows, rhs = [], []
    while len(rows) < npairs:
        P, Q = F.random_divisor(), F.random_divisor()
        try:
            xp, xq = Xof(P), Xof(Q)
            xs, xd = Xof(F.add(P, Q)), Xof(F.add(P, F.neg(Q)))
        except AssertionError:
            continue
        b3 = pow(Bval(xp, xq), 3, p)
        ma = [mono_val(xp, a, p) for a in std]
        mb = [mono_val(xq, b, p) for b in std]
        rows.append([ma[i] * mb[j] % p for i in range(36) for j in range(36)])
        rhs.append([xs[k] * xd[m] % p * b3 % p for k in range(9) for m in range(9)])
    print(f'sampled {len(rows)} pairs [{time.time() - t0:.1f}s]', flush=True)
    A = flint.nmod_mat(rows, p)
    Bm = flint.nmod_mat(rhs, p)
    # least-squares-free: take the normal equations of an overdetermined consistent system via rref of [A | Bm]
    aug = flint.nmod_mat(len(rows), 1296 + 81, [0] * (len(rows) * (1296 + 81)), p)
    for i in range(len(rows)):
        for j in range(1296):
            aug[i, j] = A[i, j]
        for j in range(81):
            aug[i, 1296 + j] = Bm[i, j]
    Rr, rk = aug.rref()
    print(f'rank of [A|b] = {rk} [{time.time() - t0:.1f}s]', flush=True)
    assert rk == 1296, 'inconsistent or underdetermined'
    sol = [[int(Rr[i, 1296 + j]) for j in range(81)] for i in range(1296)]
    # check pivots are the identity
    for i in range(1296):
        assert int(Rr[i, i]) == 1
    laws = {}
    for k in range(9):
        for m in range(9):
            laws[f'{k},{m}'] = [[list(basis[i][0]), list(basis[i][1]), sol[i][k * 9 + m]] for i in range(1296)
                                if sol[i][k * 9 + m]]
    nnz = sum(len(v) for v in laws.values())
    print(f'nonzero coefficients over all 81 (k,m): {nnz}  (mean {nnz / 81:.1f} per coordinate)')
    with open(f'laws_p{p}.json', 'w') as fh:
        json.dump({'p': p, 'std': [list(s) for s in std], 'B': Bv, 'laws': laws}, fh)
    print(f'done [{time.time() - t0:.1f}s]')


if __name__ == '__main__':
    main()
