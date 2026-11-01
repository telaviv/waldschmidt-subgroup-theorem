"""P2 assessment: smallest N with (dup_0..dup_8)_N + I_N = S_N (mod p rank via evaluation at points of A).
UNTRUSTED measurement."""
import itertools, sys, os, random
import flint
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from g1_measure import load_laws, chart_pt, Xof, P, ev_law
laws = load_laws()
def stdmon(N):   # a basis of (S/I)_N would be needed; use all monomials and compute rank of span directly
    return list(itertools.combinations_with_replacement(range(9), N))
for N in (5, 6, 7, 8):
    target = 9 * N * N
    npts = target + 40
    pts = [Xof(chart_pt()[0]) for _ in range(npts)]
    monsN4 = stdmon(N - 4)
    rows = []
    for k in range(9):
        dk = [ev_law(laws[(k, 4)], X, X) for X in pts]
        for m in monsN4:
            rows.append([dk[t] * eval_m(pts[t], m) % P for t in range(npts)] if False else
                        [dk[t] * (lambda X: __import__('functools').reduce(lambda a, i: a * X[i] % P, m, 1))(pts[t]) % P
                         for t in range(npts)])
    M = flint.nmod_mat(rows, P)
    rk = M.rank()
    print(f'N = {N}: rank of (dup)_N on A = {rk} of dim (S/I)_N = {target}', flush=True)
