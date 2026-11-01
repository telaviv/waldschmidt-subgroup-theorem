"""A0b step 6: numerical (mod a fresh prime) checks of the exact laws in laws_Q.json against Cantor's algorithm.

  * law agreement: [A^{(m)}(X(P), X(Q))] = [X(P + Q)] (Cantor) for all 9 laws, random P, Q;
  * origin: O = [A^{(m)}(X(P), X(-P))];
  * duplication: Dup(X) := A^{(m0)}(X, X), m0 with X_{m0}(O) != 0, equals [X(2P)];
  * law at O: A^{(m)}(X, O) ~ X;
  * exceptional sets: A^{(m)}(P, Q) = 0 iff X_m(P - Q) = 0, tested on Q = P - T with T on div(X_m) (m = 0: T in Theta).
These are [Numerical] checks (mod p, random points), not proofs.
Usage: python checks_modp.py p
"""
import json
import random
import sys
from jac import Fp, X_eval_fn

NEG = [1, 1, 1, 1, -1, -1, -1, -1, 1]


def load_laws(p):
    lq = json.load(open('laws_Q.json'))
    laws = {}
    for key, terms in lq['laws'].items():
        k, m = map(int, key.split(','))
        tl = []
        for e, c in terms:
            num, den = (c.split('/') + ['1'])[:2]
            tl.append((e, int(num) * pow(int(den), -1, p) % p))
        laws[(k, m)] = tl
    return laws


def ev_law(tl, x, y, p):
    s = 0
    for e, c in tl:
        t = c
        for i in range(9):
            if e[i]:
                t = t * pow(x[i], e[i], p) % p
            if e[9 + i]:
                t = t * pow(y[i], e[9 + i], p) % p
        s += t
    return s % p


def proj_eq(u, v, p):
    return all((u[i] * v[j] - u[j] * v[i]) % p == 0 for i in range(9) for j in range(9))


def main():
    p = int(sys.argv[1])
    random.seed(7)
    F = Fp(p)
    ev = X_eval_fn(p)
    laws = load_laws(p)
    X = lambda D: ev(F.mumford_coords(D))
    bad = 0
    for trial in range(30):
        P, Q = F.random_divisor(), F.random_divisor()
        xp, xq, xs = X(P), X(Q), X(F.add(P, Q))
        for m in range(9):
            a = [ev_law(laws[(k, m)], xp, xq, p) for k in range(9)]
            if any(a) and not proj_eq(a, xs, p):
                bad += 1
    print('law agreement with Cantor (30 pairs x 9 laws): failures =', bad)
    # origin
    P = F.random_divisor()
    xp = X(P)
    xm = [NEG[i] * xp[i] % p for i in range(9)]
    O = None
    for m in range(9):
        a = [ev_law(laws[(k, m)], xp, xm, p) for k in range(9)]
        if any(a):
            inv = pow(next(v for v in a if v), -1, p)
            O = [v * inv % p for v in a]
            print('origin from law', m, ':', O)
            break
    m0 = [i for i in range(9) if O[i]]
    print('nonzero coordinates of O:', m0)
    # duplication
    bad = 0
    for trial in range(20):
        P = F.random_divisor()
        xp, x2 = X(P), X(F.add(P, P))
        d = [ev_law(laws[(k, m0[0])], xp, xp, p) for k in range(9)]
        if not any(d) or not proj_eq(d, x2, p):
            bad += 1
    print(f'duplication Dup = A^({m0[0]})(X, X) vs Cantor doubling (20 points): failures = {bad}')
    # law at O
    bad = 0
    for trial in range(10):
        P = F.random_divisor()
        xp = X(P)
        for m in range(9):
            a = [ev_law(laws[(k, m)], xp, O, p) for k in range(9)]
            if any(a) and not proj_eq(a, xp, p):
                bad += 1
    print('A^(m)(X, O) ~ X (10 points x 9 laws): failures =', bad)
    # exceptional set of law 0: Q = P - T, T in Theta  => A^(0)(P, Q) = 0
    zeros = 0
    for trial in range(10):
        P, T = F.random_divisor(), F.random_theta_point()
        Q = F.add(P, F.neg(T))
        try:
            xq = X(Q)
        except AssertionError:
            continue
        a = [ev_law(laws[(k, 0)], X(P), xq, p) for k in range(9)]
        zeros += (not any(a))
    print('law 0 vanishes identically at (P, P - T), T in Theta: ', zeros, '/ 10')


if __name__ == '__main__':
    main()
