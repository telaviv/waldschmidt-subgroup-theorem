"""Anchor computation in Q(alpha), alpha^5 = 2 (UNTRUSTED; every claim is re-checked in Lean).

D0 = (0, -1) + (alpha, 3) has Mumford form u = x(x - alpha), v = 2 alpha^4 x - 1.  We compute 2 D0 by Cantor
(exact, in Q[alpha]/(alpha^5 - 2)), its Mumford coordinates m2 = (s1, s2, b1, b0), then
  law0(grantJ m2, negP P0) = 32 A^{(0)}(grantJ m2, negP P0)   (A1's lawPt 0, data laws_Q.json)
and check it equals lam * P0 with lam != 0.  Also: the discriminant of U, the value
b0^2 + s1 b0 b1 + s2 b1^2 (nonzero <=> no point of D2 has y = 0) and the inverses of all elements that must be
nonzero (Lean proves nonvanishing by e * e^{-1} = 1 + c (alpha^5 - 2)).
Writes anchor.json.
"""
import json
import os
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
SPIKE = os.path.join(HERE, '..', 'abvar_spike')

# ---- arithmetic in K = Q[a]/(a^5 - 2): elements are lists of 5 Fractions


def kred(p):
    p = list(p) + [Fr(0)] * max(0, 5 - len(p))
    for d in range(len(p) - 1, 4, -1):
        c = p[d]
        if c:
            p[d - 5] += 2 * c
            p[d] = Fr(0)
    return [Fr(x) for x in p[:5]]


def kmul(a, b):
    r = [Fr(0)] * 9
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return kred(r)


def kadd(a, b):
    return [x + y for x, y in zip(a, b)]


def ksub(a, b):
    return [x - y for x, y in zip(a, b)]


def kc(c):
    return [Fr(c)] + [Fr(0)] * 4


A = [Fr(0), Fr(1), Fr(0), Fr(0), Fr(0)]
K0, K1 = kc(0), kc(1)


def kpow(a, n):
    r = K1
    for _ in range(n):
        r = kmul(r, a)
    return r


def kinv(a):
    """inverse by solving the 5x5 linear system (multiplication matrix)"""
    import sympy as sp
    M = sp.zeros(5, 5)
    for j in range(5):
        col = kmul(a, [Fr(int(i == j)) for i in range(5)])
        for i in range(5):
            M[i, j] = sp.Rational(col[i].numerator, col[i].denominator)
    sol = M.LUsolve(sp.Matrix([1, 0, 0, 0, 0]))
    r = [Fr(int(sp.Rational(s).p), int(sp.Rational(s).q)) for s in sol]
    assert kmul(a, r) == K1
    return r


def kiszero(a):
    return all(x == 0 for x in a)

# ---- polynomials in x over K: lists of K elements (low degree first)


def ptrim(p):
    while p and kiszero(p[-1]):
        p = p[:-1]
    return p


def padd(p, q):
    n = max(len(p), len(q))
    return ptrim([kadd(p[i] if i < len(p) else K0, q[i] if i < len(q) else K0) for i in range(n)])


def psub(p, q):
    n = max(len(p), len(q))
    return ptrim([ksub(p[i] if i < len(p) else K0, q[i] if i < len(q) else K0) for i in range(n)])


def pmul(p, q):
    if not p or not q:
        return []
    r = [K0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] = kadd(r[i + j], kmul(x, y))
    return ptrim(r)


def pscale(p, c):
    return ptrim([kmul(x, c) for x in p])


def pdivmod(p, q):
    p = ptrim(p)
    q = ptrim(q)
    inv = kinv(q[-1])
    quo = [K0] * max(1, len(p) - len(q) + 1)
    while len(p) >= len(q) and p:
        c = kmul(p[-1], inv)
        d = len(p) - len(q)
        quo[d] = c
        p = psub(p, [K0] * d + pscale(q, c))
    return ptrim(quo), p


def pmod(p, q):
    return pdivmod(p, q)[1]


f = [kc(1), K0, K0, K0, K0, kc(4)]
u = [K0, ksub(K0, A), K1]                      # x^2 - a x
v = [kc(-1), kmul(kc(2), kpow(A, 4))]          # 2 a^4 x - 1
assert pmod(psub(f, pmul(v, v)), u) == []
# Cantor doubling: U = u^2, V = v + u k with V^2 = f mod u^2
# (f - v^2)/u = q;  2 v k = q mod u  ->  k = q * (2v)^{-1} mod u
qq, r = pdivmod(psub(f, pmul(v, v)), u)
assert r == []
# inverse of 2v mod u by extended Euclid (u quadratic, 2v linear)


def pinvmod(a, m):
    # solve (s0 + s1 x) a = 1 mod m, m monic quadratic: linear system over K
    import itertools
    # brute: represent unknown s = s0 + s1 x; compute a*1 mod m and a*x mod m
    c0 = pmod(a, m)
    c1 = pmod(pmul(a, [K0, K1]), m)
    def co(p, i):
        return p[i] if i < len(p) else K0
    # [co(c0,0) co(c1,0)] [s0]   [1]
    # [co(c0,1) co(c1,1)] [s1] = [0]
    a11, a12, a21, a22 = co(c0, 0), co(c1, 0), co(c0, 1), co(c1, 1)
    det = ksub(kmul(a11, a22), kmul(a12, a21))
    di = kinv(det)
    s0 = kmul(a22, di)
    s1 = kmul(ksub(K0, a21), di)
    s = ptrim([s0, s1])
    assert pmod(pmul(s, a), m) == [K1]
    return s


k = pmod(pmul(qq, pinvmod(pscale(v, kc(2)), u)), u)
U = pmul(u, u)
V = padd(v, pmul(u, k))
assert pmod(psub(f, pmul(V, V)), U) == []
while len(U) - 1 > 2:
    Uq, r = pdivmod(psub(f, pmul(V, V)), U)
    assert r == []
    U = pscale(Uq, kinv(Uq[-1]))
    V = pmod(pscale(V, kc(-1)), U)
assert len(U) == 3 and pmod(psub(f, pmul(V, V)), U) == []
s1 = ksub(K0, U[1])
s2 = U[0]
b1 = V[1] if len(V) > 1 else K0
b0 = V[0]
m2 = [s1, s2, b1, b0]
print('s1 =', s1, '\ns2 =', s2, '\nb1 =', b1, '\nb0 =', b0)

# chart relations (Lean chartR1J / chartR0J)


def chartR1(p):
    p0, p1, p2, p3 = p
    t = kmul(kc(-2), kmul(p3, p2))
    t = ksub(t, kmul(kmul(p2, p2), p0))
    t = kadd(t, kmul(kc(4), kpow(p0, 4)))
    t = ksub(t, kmul(kc(12), kmul(kmul(p0, p0), p1)))
    t = kadd(t, kmul(kc(4), kmul(p1, p1)))
    return t


def chartR0(p):
    p0, p1, p2, p3 = p
    t = ksub(K0, kmul(p3, p3))
    t = kadd(t, kmul(kmul(p2, p2), p1))
    t = ksub(t, kmul(kc(4), kmul(kpow(p0, 3), p1)))
    t = kadd(t, kmul(kc(8), kmul(p0, kmul(p1, p1))))
    return kadd(t, K1)


assert kiszero(chartR1(m2)) and kiszero(chartR0(m2))


def grantJ(m):
    m0, m1, m2_, m3 = m
    h = Fr(1, 4)
    return [K1,
            kadd(ksub(kmul(kc(h), kmul(m2_, m2_)), kpow(m0, 3)), kmul(m0, m1)),
            ksub(K0, m1),
            m0,
            kadd(kadd(kadd(kadd(kmul(kc(-2), kmul(m3, kmul(m0, m0))), kmul(m3, m1)),
                           kmul(kc(-h), kpow(m2_, 3))), kmul(m2_, kpow(m0, 3))),
                 kmul(kc(-3), kmul(m2_, kmul(m0, m1)))),
            ksub(ksub(K0, kmul(m3, m0)), kmul(m2_, m1)),
            m3,
            m2_,
            kadd(kmul(kc(Fr(1, 2)), kmul(m3, m2_)), kmul(kc(2), kmul(kmul(m0, m0), m1)))]


def negP(x):
    return [x[0], x[1], x[2], x[3]] + [ksub(K0, t) for t in x[4:8]] + [x[8]]


P0m = [A, K0, kmul(kc(2), kpow(A, 4)), kc(-1)]   # mumfordPts' 0 (-1) a 3 = (a, 0, 4/a, -1)
# check against Special.lean: (1, a^3, 0, a, -2a^2, a, -1, 2a^4, -a^4)
P0 = grantJ(P0m)
assert P0 == [K1, kpow(A, 3), K0, A, kmul(kc(-2), kpow(A, 2)), A, kc(-1), kmul(kc(2), kpow(A, 4)),
              ksub(K0, kpow(A, 4))], P0

lq = json.load(open(os.path.join(SPIKE, 'laws_Q.json')))
LAW = {}
for key, terms in lq['laws'].items():
    kk, mm = map(int, key.split(','))
    LAW[(kk, mm)] = [(e, Fr(c)) for e, c in terms]


def law0(x, y):
    out = []
    for kk in range(9):
        s = K0
        for e, c in LAW[(kk, 0)]:
            t = kc(32 * c)
            for i in range(9):
                if e[i]:
                    t = kmul(t, kpow(x[i], e[i]))
                if e[9 + i]:
                    t = kmul(t, kpow(y[i], e[9 + i]))
            s = kadd(s, t)
        out.append(s)
    return out


chk = law0(P0, negP(P0))
assert chk[4] == kmul(kc(128), A) and all(kiszero(chk[i]) for i in range(9) if i != 4), chk
G2 = grantJ(m2)
L = law0(G2, negP(P0))
lam = L[0]
print('lam =', lam)
assert not kiszero(lam)
for i in range(9):
    assert L[i] == kmul(lam, P0[i]), i
disc = ksub(kmul(s1, s1), kmul(kc(4), s2))
yv = kadd(kadd(kmul(b0, b0), kmul(s1, kmul(b0, b1))), kmul(s2, kmul(b1, b1)))
print('disc =', disc, '\nyval =', yv)


def fs(a):
    return [str(x) for x in a]


json.dump({'s1': fs(s1), 's2': fs(s2), 'b1': fs(b1), 'b0': fs(b0), 'G2': [fs(g) for g in G2],
           'lam': fs(lam), 'lam_inv': fs(kinv(lam)), 'disc': fs(disc), 'disc_inv': fs(kinv(disc)),
           'yval': fs(yv), 'yval_inv': fs(kinv(yv)), 'b1_inv': fs(kinv(b1)) if not kiszero(b1) else None},
          open(os.path.join(HERE, 'anchor.json'), 'w'), indent=1)
print('ok: law0(grantJ m2, negP P0) = lam * P0, lam != 0')
