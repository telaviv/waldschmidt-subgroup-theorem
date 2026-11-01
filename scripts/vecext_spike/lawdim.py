"""Dimension of the space of addition laws of bidegree (c,c) on E^natural, over F_p, random g2, g3.
Model '5': coordinates (U,V,W,T1,T3); model '6': (U,V,W,T1,T2,T3), T1 = W t, T2 = U t, T3 = V t - 2U^2/W.
A law = tuple (A_j) of bidegree (c,c) forms with A_j(P,Q) = A_W(P,Q) * X_j(P+Q) on E^nat x E^nat
(W-normalised representatives).  Computed as the nullspace of evaluation equations at random points.
Usage: python lawdim.py model c [seed]
"""
import sys, random, itertools
from flint import nmod_mat, nmod

p = 1000000007  # p = 3 mod 4
model = sys.argv[1]; c = int(sys.argv[2]); seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
random.seed(seed)
g2 = random.randrange(p); g3 = random.randrange(p)
inv = lambda a: pow(a % p, p - 2, p)

def coords(x, y, t):
    T1 = t; T2 = x*t % p; T3 = (y*t - 2*x*x) % p
    if model == '5':
        return [x % p, y % p, 1, T1 % p, T3]
    return [x % p, y % p, 1, T1 % p, T2, T3]

nv = 5 if model == '5' else 6
def rand_point():
    while True:
        x = random.randrange(p)
        f = (4*x**3 - g2*x - g3) % p
        if pow(f, (p - 1)//2, p) == 1:
            y = pow(f, (p + 1)//4, p)
            if random.random() < .5: y = p - y
            return x, y, random.randrange(p)

def add(P, Q):
    (x1, y1, t1), (x2, y2, t2) = P, Q
    m = (y1 - y2) * inv(x1 - x2) % p
    x3 = (m*m*inv(4) - x1 - x2) % p
    y3 = (-m*(x3 - x1) - y1) % p
    t3 = (t1 + t2 - m*inv(2)) % p
    return x3, y3, t3

monos = [e for e in itertools.product(range(c + 1), repeat=nv) if sum(e) == c]
def mono_vals(X):
    out = []
    for e in monos:
        v = 1
        for xi, ei in zip(X, e):
            v = v * pow(xi, ei, p) % p
        out.append(v)
    return out

# basis of R_c: independent monomials as functions on E^nat
pts = [rand_point() for _ in range(3*len(monos) + 20)]
Mv = nmod_mat([mono_vals(coords(*P)) for P in pts], p)
R, rk = Mv.rref()
piv = []
for i in range(rk):
    for j in range(len(monos)):
        if int(R[i, j]) != 0:
            piv.append(j); break
print('model', model, 'c', c, 'dim R_c =', rk, 'of', len(monos), 'monomials', flush=True)
nb = rk
nunk = nv * nb * nb
npts = nunk // (nv - 1) + 40
rows = []
for _ in range(npts):
    P = rand_point(); Q = rand_point()
    S = add(P, Q)
    bP = [mono_vals(coords(*P))[j] for j in piv]
    bQ = [mono_vals(coords(*Q))[j] for j in piv]
    prod = [a*b % p for a in bP for b in bQ]
    XS = coords(*S)
    widx = 2
    for j in range(nv):
        if j == widx: continue
        row = [0]*nunk
        for k, v in enumerate(prod):
            row[j*nb*nb + k] = v
            row[widx*nb*nb + k] = (-v * XS[j]) % p
        rows.append(row)
A = nmod_mat(rows, p)
rkA = A.rank()
print('unknowns', nunk, 'equations', len(rows), 'rank', rkA, 'dim of law space =', nunk - rkA, flush=True)
