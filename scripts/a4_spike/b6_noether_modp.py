"""A4 spike (UNTRUSTED, mod p): a Groebner-free route to B6 (Hilbert upper bound of the A-block slice).

For three linear forms y_1, y_2, y_3 (coordinate choices or random), test whether
    (S/I_A)_n = y_1 (S/I_A)_{n-1} + y_2 (S/I_A)_{n-1} + y_3 (S/I_A)_{n-1}
by rank of {y_j * m : |m| = n-1} evaluated at points of A (target 9 n^2).  If it holds at n = n0 it holds for all
n >= n0 (multiply by monomials), so (S/I_A)_n is spanned by y^a * (degree n0-1 monomials), and
dim (S/I_A)_n <= dim(S/I_A)_{n0-1} * C(n - n0 + 3, 2): a quadratic bound from ONE degree-n0 certificate.
Usage: python b6_noether_modp.py
"""
import itertools, os, sys, random
import flint
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'jac'))
from g1_measure import chart_pt, Xof, P

random.seed(5)
pts = [Xof(chart_pt()[0]) for _ in range(9 * 49 + 60)]


def monos(d):
    return list(itertools.combinations_with_replacement(range(9), d))


def ev(x, m):
    r = 1
    for i in m:
        r = r * x[i] % P
    return r


cands = {'X0,X4,X8': [{0: 1}, {4: 1}, {8: 1}],
         'X0,X1,X4': [{0: 1}, {1: 1}, {4: 1}],
         'X0,X2,X3': [{0: 1}, {2: 1}, {3: 1}],
         'random': [{i: random.randrange(1, 100) for i in range(9)} for _ in range(3)]}
for name, ys in cands.items():
    for n in (3, 4, 5, 6):
        target = 9 * n * n
        npts = target + 40
        yv = [[sum(c * x[i] for i, c in y.items()) % P for x in pts[:npts]] for y in ys]
        rows = []
        for m in monos(n - 1):
            mv = [ev(x, m) for x in pts[:npts]]
            for y in yv:
                rows.append([a * b % P for a, b in zip(y, mv)])
        rk = flint.nmod_mat(rows, P).rank()
        print(f'y = {name}: n = {n}: rank (y)(S/I)_(n-1) = {rk} / {target}', flush=True)
        if rk == target:
            break
