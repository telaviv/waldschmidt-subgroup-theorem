"""A4 spike (UNTRUSTED, mod p): size of the B5 local-CI certificates for the A-block.

For k random choices F_i = (F_{i,1..6}) of integer combinations of the 9 quadrics:
  * the colon ((F_i) : I_A) in degree 3 (S with S*Q_j in (F_i)_5 for the 9 quadrics and S*C_j in (F_i)_6 for the 3
    extra cubics), and the colon elements not vanishing on A;
  * the least N with (S_{all i})_N + I_N = S_N (rank 9 N^2 by evaluation at points of A): the degree of the
    single-copy Nullstellensatz certificate x_v^N in I_A + (S) that the cover lemma of STAGE_A4_BEZOUT needs.
Usage: python b5_cover_modp.py kmax Nmax
"""
import itertools, json, os, sys, random
import flint
HERE = os.path.dirname(os.path.abspath(__file__))
JAC = os.path.join(HERE, '..', 'jac')
sys.path.insert(0, JAC)
from g1_measure import chart_pt, Xof, P
SPIKE = os.path.join(HERE, '..', 'abvar_spike')
quads = [{tuple(sorted(m)): c for m, c in q} for q in json.load(open(os.path.join(SPIKE, 'ideal.json')))['quadrics']]


def monos(d):
    return list(itertools.combinations_with_replacement(range(9), d))


def ev(x, m):
    r = 1
    for i in m:
        r = r * x[i] % P
    return r


def mulmat(G, d):
    """matrix of S -> S*G, S of degree d, in the monomial basis of degree d + deg G."""
    e = d + len(next(iter(G)))
    ms, mt = monos(d), monos(e)
    idx = {m: i for i, m in enumerate(mt)}
    M = flint.nmod_mat(len(ms), len(mt), P)
    for a, sm in enumerate(ms):
        for k, c in G.items():
            j = idx[tuple(sorted(k + sm))]
            M[a, j] = (int(M[a, j]) + c) % P
    return M


def ideal_span(F, e):
    """rows: F_k * monomials of degree e - 2."""
    mt = monos(e)
    idx = {m: i for i, m in enumerate(mt)}
    rows = []
    for f in F:
        for sm in monos(e - 2):
            r = [0] * len(mt)
            for k, c in f.items():
                j = idx[tuple(sorted(k + sm))]
                r[j] = (r[j] + c) % P
            rows.append(r)
    return flint.nmod_mat(rows, P)


def left_kernel(M):
    X, nul = M.transpose().nullspace()
    return [[int(X[i, j]) for i in range(X.nrows())] for j in range(nul)]


random.seed(3)
pts = [Xof(chart_pt()[0]) for _ in range(9 * 12 * 12 + 60)]
# cubics: complement of (Q)_3 in I_3 by evaluation
m3 = monos(3)
E3 = flint.nmod_mat([[ev(x, m) for x in pts[:300]] for m in m3], P)
I3 = left_kernel(E3)                    # basis of I_3
print('dim I_3 =', len(I3), '(expected 84)', flush=True)
Q3 = ideal_span([{k: v % P for k, v in q.items()} for q in quads], 3)
rowsQ3 = [[int(Q3[i, j]) for j in range(Q3.ncols())] for i in range(Q3.nrows())]
base = flint.nmod_mat(rowsQ3, P).rank()
cubics = []
for vec in I3:
    if flint.nmod_mat(rowsQ3 + [vec], P).rank() > base:
        rowsQ3.append(vec)
        base += 1
        cubics.append({m3[a]: v for a, v in enumerate(vec) if v})
print('dim (Q)_3 =', Q3.rank(), ', extra cubics:', len(cubics), flush=True)

kmax, Nmax = int(sys.argv[1]), int(sys.argv[2])
Ss = []
for trial in range(kmax):
    F = []
    for _ in range(6):
        co = [random.randint(-3, 3) for _ in quads]
        f = {}
        for c, q in zip(co, quads):
            for k, v in q.items():
                f[k] = (f.get(k, 0) + c * v)
        F.append({k: v % P for k, v in f.items() if v % P})
    K5, n5 = ideal_span(F, 5).nullspace()
    K6, n6 = ideal_span(F, 6).nullspace()
    K5 = flint.nmod_mat([[int(K5[i, j]) for j in range(n5)] for i in range(K5.nrows())], P)
    K6 = flint.nmod_mat([[int(K6[i, j]) for j in range(n6)] for i in range(K6.nrows())], P)
    blocks = [mulmat(q, 3) * K5 for q in quads] + [mulmat(c, 3) * K6 for c in cubics]
    rows = [[int(B[a, j]) for B in blocks for j in range(B.ncols())] for a in range(len(m3))]
    colon = left_kernel(flint.nmod_mat(rows, P))
    outside = []
    for vec in colon:
        vals = [sum(v * ev(x, m3[a]) for a, v in enumerate(vec) if v) % P for x in pts[:30]]
        if any(vals):
            outside.append(vec)
    # rank of the outside part modulo I_3
    Eo = flint.nmod_mat([[sum(v * ev(x, m3[a]) for a, v in enumerate(vec) if v) % P for x in pts[:200]]
                         for vec in outside], P) if outside else None
    rko = Eo.rank() if outside else 0
    print(f'choice {trial}: dim colon_3 = {len(colon)}, colon elements outside I_A: rank {rko} mod I_3', flush=True)
    Ss += outside
    # cover degree with the S's so far
    for N in range(3, Nmax + 1):
        target = 9 * N * N
        npts = target + 40
        mons = monos(N - 3)
        Sval = [[sum(v * ev(x, m3[a]) for a, v in enumerate(vec) if v) % P for x in pts[:npts]] for vec in Ss]
        Mval = [[ev(x, m) for x in pts[:npts]] for m in mons]
        rowsN = [[s[t] * mm[t] % P for t in range(npts)] for s in Sval for mm in Mval]
        rk = flint.nmod_mat(rowsN, P).rank()
        print(f'   with {trial + 1} choice(s): N = {N}: rank (S)_N on A = {rk} / {target}', flush=True)
        if rk == target:
            break
