"""Stage A1: measurement of G1 (law 0 vs Cantor on chart x chart) and of the alternative "flow" identities.
UNTRUSTED measurement script (numbers reported in STAGE_A1.md).

Part 1 (G1, as specified in ABVAR §A0.3): for the 4 Mumford coordinates c in {s1, s2, b1, b0} of the Cantor sum
R = P + Q (generic case gcd(a_P, a_Q) = 1, one composition + one reduction step):
    E_c = A_k^(0)(X(P), X(Q)) * Den_c  -  A_0^(0)(X(P), X(Q)) * Num_c      (k = 3, 2, 7, 6 for s1, -s2, b1, b0)
must vanish modulo the chart relations of P and Q (8 variables, 4 relations). We report term counts of Num/Den,
of the pulled-back law, and of E_c before reduction (a lower bound for any certificate), and verify E_c = 0 at random
chart points mod p.

Part 2 (flow identities): with the invariant vector fields D_j (j = 1, 2) of J written on P^8 as
d/dz_j (X_i / X_0) = W_ji(X) / X_0^2 (W_ji quadratic, found by interpolation mod p and rational reconstruction),
    H_jl = B * G_jl - 3 * G_Bj * A_l^(0)    (bidegree (4, 4)),
    G_jl = Y0 sum_i dA_l/dX_i W_ji(X) - X0 sum_i dA_l/dY_i W_ji(Y),   G_Bj likewise for B,
expresses "A_l^(0)(X^, Y^) / B(X^, Y^)^3 is invariant under (u, v) -> (u + t e_j, v - t e_j)". We check H_jl = 0 at
random pairs of chart points mod p and report the checker weight (`wsum`) and term counts.
"""
import json
import os
import random
import sys
import time

import flint
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
SPIKE = os.path.join(HERE, '..', 'abvar_spike')
sys.path.insert(0, SPIKE)

P = 1000003
random.seed(7)


def fsqrt(a, p=P):
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    # Tonelli-Shanks
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def curve_pt():
    while True:
        x = random.randrange(P)
        y = fsqrt(4 * pow(x, 5, P) + 1)
        if y:
            return x, y


def chart_pt():
    (x1, y1), (x2, y2) = curve_pt(), curve_pt()
    while x1 == x2:
        x2, y2 = curve_pt()
    inv = pow(x1 - x2, -1, P)
    return ((x1 + x2) % P, x1 * x2 % P, (y1 - y2) * inv % P, (x1 * y2 - x2 * y1) * inv % P), (x1, y1, x2, y2)


def Xof(c):
    s1, s2, b1, b0 = c
    i4, i2 = pow(4, -1, P), pow(2, -1, P)
    return [1, (b1 * b1 * i4 - s1 ** 3 + s1 * s2) % P, -s2 % P, s1,
            (-2 * b0 * s1 * s1 + b0 * s2 - b1 ** 3 * i4 + b1 * s1 ** 3 - 3 * b1 * s1 * s2) % P,
            (-b0 * s1 - b1 * s2) % P, b0, b1, (b0 * b1 * i2 + 2 * s1 * s1 * s2) % P]


def load_laws():
    lq = json.load(open(os.path.join(SPIKE, 'laws_Q.json')))
    laws = {}
    for key, terms in lq['laws'].items():
        k, m = map(int, key.split(','))
        laws[(k, m)] = [(tuple(e[:9]), tuple(e[9:]), sp.Rational(c)) for e, c in terms]
    return laws


def ev_law(law, X, Y, p=P):
    s = 0
    for ex, ey, c in law:
        t = c.p * pow(c.q, -1, p)
        for i in range(9):
            t = t * pow(X[i], ex[i], p) * pow(Y[i], ey[i], p)
        s += t
    return s % p


# ------------------------------------------------------------------------------------------- Part 1: G1 sizes
def part1(laws):
    print('=== Part 1: G1 (law 0 vs Cantor) ===')
    x = sp.Symbol('x')
    s1, s2, b1, b0, t1, t2, c1, c0 = sp.symbols('s1 s2 b1 b0 t1 t2 c1 c0')
    a1, bb1 = x ** 2 - s1 * x + s2, b1 * x + b0
    a2, bb2 = x ** 2 - t1 * x + t2, c1 * x + c0
    f = 4 * x ** 5 + 1
    t0 = time.time()
    # CRT: c = b1 + a1 * k, k = (bb2 - bb1) * inv(a1) mod a2 ; inv via resultant adjugate
    res = sp.resultant(a1, a2, x)
    s_, t_, h = sp.gcdex(a1, a2, x)          # s a1 + t a2 = h (h = 1 over the fraction field)
    k = sp.rem(sp.expand((bb2 - bb1) * s_), a2, x)
    c = sp.expand(bb1 + a1 * k)
    num, den = sp.fraction(sp.together(c))
    cpoly = sp.Poly(sp.expand(num), x)
    print(f'  CRT cubic: numerator coefficients {[len(sp.Add.make_args(co)) for co in cpoly.all_coeffs()]} terms, '
          f'denominator {len(sp.Add.make_args(sp.expand(den)))} terms  [{time.time() - t0:.1f}s]')
    # f*den^2 - num^2 = a1 a2 q (mod relations): polynomial quotient
    F = sp.Poly(sp.expand(f * den ** 2 - num ** 2), x)
    q, r = sp.div(F, sp.Poly(sp.expand(a1 * a2), x))
    qc = q.all_coeffs()            # degree 2: q2 x^2 + q1 x + q0
    q2, q1, q0 = [sp.expand(z) for z in qc]
    # a_R = x^2 - sR1 x + sR2 = q / q2 ; b_R = -c mod a_R
    sR1n, sR1d = sp.expand(-q1), q2
    sR2n, sR2d = q0, q2
    print(f'  q coefficients: {[len(sp.Add.make_args(z)) for z in (q2, q1, q0)]} terms  [{time.time() - t0:.1f}s]')
    # b_R = -(num/den) mod (x^2 - sR1 x + sR2): with aR = (q2 x^2 + q1 x + q0)/q2
    # remainder of num modulo q (q2 x^2 + q1 x + q0) over Q(q2): multiply by q2^2 (deg num = 3)
    numP = sp.Poly(num, x)
    qP = sp.Poly(q2 * x ** 2 + q1 * x + q0, x)
    rr = sp.prem(numP, qP)           # q2^(3-2+1) * num = Q * q + rr
    rc = rr.all_coeffs()
    rb1, rb0 = (sp.expand(rc[0]), sp.expand(rc[1])) if len(rc) == 2 else (0, sp.expand(rc[0]))
    # b_R = -rr / (q2^2 * den)
    sizes = {'s1': (sR1n, sR1d), 's2': (sR2n, sR2d), 'b1': (-rb1, q2 ** 2 * den), 'b0': (-rb0, q2 ** 2 * den)}
    for nm, (n_, d_) in sizes.items():
        print(f'  Cantor {nm}(R): numerator {len(sp.Add.make_args(sp.expand(n_)))} terms, '
              f'denominator {len(sp.Add.make_args(sp.expand(d_)))} terms (unreduced)')
    # pulled-back law 0
    names = ('s1', 's2', 'b1', 'b0', 't1', 't2', 'c1', 'c0')
    ctx = flint.fmpq_mpoly_ctx.get(names, 'degrevlex')
    g = ctx.gens()
    one = ctx.from_dict({tuple([0] * 8): 1})

    def Xpoly(S1, S2, B1, B0):
        return [one, B1 ** 2 / 4 - S1 ** 3 + S1 * S2, -S2, S1, -2 * B0 * S1 ** 2 + B0 * S2 - B1 ** 3 / 4 + B1 * S1 ** 3 -
                3 * B1 * S1 * S2, -B0 * S1 - B1 * S2, B0, B1, B0 * B1 / 2 + 2 * S1 ** 2 * S2]
    XD, XE = Xpoly(*g[:4]), Xpoly(*g[4:])
    A = {}
    for kk in (0, 2, 3, 6, 7):
        acc = ctx.from_dict({})
        for ex, ey, cc in laws[(kk, 0)]:
            t = one * flint.fmpq(int(cc.p), int(cc.q))
            for i in range(9):
                for _ in range(ex[i]):
                    t = t * XD[i]
                for _ in range(ey[i]):
                    t = t * XE[i]
            acc = acc + t
        A[kk] = acc
        print(f'  law 0 pulled back: A_{kk}^(0) has {len(acc.monoms())} terms')

    def to_flint(e):
        pe = sp.Poly(sp.expand(e), *sp.symbols(names))
        return ctx.from_dict({m: flint.fmpq(int(cf.p), int(cf.q)) for m, cf in zip(pe.monoms(), pe.coeffs())})
    out = {}
    for nm, kk, sign in (('s1', 3, 1), ('s2', 2, -1), ('b1', 7, 1), ('b0', 6, 1)):
        n_, d_ = sizes[nm]
        Nf, Df = to_flint(sign * n_), to_flint(d_)
        t1_ = time.time()
        E = A[kk] * Df - A[0] * Nf
        pairs = len(A[kk].monoms()) * len(Df.monoms()) + len(A[0].monoms()) * len(Nf.monoms())
        out[nm] = dict(num=len(Nf.monoms()), den=len(Df.monoms()), E_terms=len(E.monoms()), term_pairs=pairs,
                       deg=E.total_degree())
        print(f'  G1[{nm}]: E has {len(E.monoms())} terms (total degree {E.total_degree()}), '
              f'{pairs} term-pairs to form it  [{time.time() - t1_:.1f}s]')
    # numerical check at random chart points (E must vanish at points of chart x chart over F_p)
    Es = {}
    for nm, kk, sign in (('s1', 3, 1), ('s2', 2, -1), ('b1', 7, 1), ('b0', 6, 1)):
        n_, d_ = sizes[nm]
        Es[nm] = A[kk] * to_flint(d_) - A[0] * to_flint(sign * n_)
    good = 0
    for _ in range(5):
        cP, _ = chart_pt()
        cQ, _ = chart_pt()
        vals = [flint.fmpq(v) for v in cP + cQ]
        allz = True
        for nm, E in Es.items():
            v = E(*vals)
            allz &= (int(v.p) * pow(int(v.q), -1, P)) % P == 0
        good += allz
    print(f'  G1 identities vanish at {good}/5 random chart pairs mod p')
    return out


# ------------------------------------------------------------------------------------------- Part 2: flow identities
def vector_fields_numeric(npts=400):
    """Values of d/dz_j of (s1, s2, b1, b0) at random points, from the inverse Abel Jacobian."""
    data = []
    for _ in range(npts):
        c, (x1, y1, x2, y2) = chart_pt()
        d = pow(x2 - x1, -1, P)
        dx = {(1, 1): y1 * x2 * d, (1, 2): -y1 * d, (2, 1): -y2 * x1 * d, (2, 2): y2 * d}   # dx_i / dz_j
        fp = lambda xx: 20 * pow(xx, 4, P)
        dy = {(i, j): fp(xi) * pow(2 * yi, -1, P) * dx[(i, j)] % P for (i, j) in dx for xi, yi in [((x1, y1), (x2, y2))[i - 1]]}
        out = {}
        inv = pow(x1 - x2, -1, P)
        for j in (1, 2):
            ds1 = (dx[(1, j)] + dx[(2, j)]) % P
            ds2 = (dx[(1, j)] * x2 + x1 * dx[(2, j)]) % P
            # b1 = (y1 - y2)/(x1 - x2), b0 = (x1 y2 - x2 y1)/(x1 - x2)
            num1, num0 = (y1 - y2) % P, (x1 * y2 - x2 * y1) % P
            dnum1 = (dy[(1, j)] - dy[(2, j)]) % P
            dnum0 = (dx[(1, j)] * y2 + x1 * dy[(2, j)] - dx[(2, j)] * y1 - x2 * dy[(1, j)]) % P
            dden = (dx[(1, j)] - dx[(2, j)]) % P
            db1 = (dnum1 * inv - num1 * dden * inv * inv) % P
            db0 = (dnum0 * inv - num0 * dden * inv * inv) % P
            out[j] = (ds1, ds2, db1, db0)
        data.append((c, out))
    return data


def chain_X(c, dc):
    """d X^_i from d(s1, s2, b1, b0) by the chain rule (X^ = Grant's affine coordinates)."""
    s1, s2, b1, b0 = c
    ds1, ds2, db1, db0 = dc
    i4, i2 = pow(4, -1, P), pow(2, -1, P)
    d = [0,
         2 * b1 * db1 * i4 - 3 * s1 * s1 * ds1 + ds1 * s2 + s1 * ds2,
         -ds2, ds1,
         -2 * db0 * s1 * s1 - 4 * b0 * s1 * ds1 + db0 * s2 + b0 * ds2 - 3 * b1 * b1 * db1 * i4 + db1 * s1 ** 3 +
         3 * b1 * s1 * s1 * ds1 - 3 * (db1 * s1 * s2 + b1 * ds1 * s2 + b1 * s1 * ds2),
         -db0 * s1 - b0 * ds1 - db1 * s2 - b1 * ds2, db0, db1,
         (db0 * b1 + b0 * db1) * i2 + 4 * s1 * ds1 * s2 + 2 * s1 * s1 * ds2]
    return [v % P for v in d]


def ratrec(a, p=P):
    a %= p
    r0, r1, s0, s1 = p, a, 0, 1
    import math
    bound = int(math.isqrt(p // 2))
    while r1 > bound:
        q = r0 // r1
        r0, r1, s0, s1 = r1, r0 - q * r1, s1, s0 - q * s1
    if s1 == 0 or abs(s1) > bound:
        return None
    return sp.Rational(r1 if s1 > 0 else -r1, abs(s1))


def part2(laws):
    print('=== Part 2: flow identities ===')
    quads = json.load(open(os.path.join(SPIKE, 'ideal.json')))['quadrics']
    lq = json.load(open(os.path.join(SPIKE, 'laws_Q.json')))
    std2 = [tuple(s) for s in lq['std']]
    data = vector_fields_numeric(300)
    W = {}
    for j in (1, 2):
        for i in range(1, 9):
            rows, rhs = [], []
            for c, out in data:
                X = Xof(c)
                rows.append([X[a] * X[b] % P for a, b in std2])
                rhs.append(chain_X(c, out[j])[i])
            M = flint.nmod_mat([r + [v] for r, v in zip(rows, rhs)], P)
            R, rk = M.rref()
            A_ = flint.nmod_mat(rows, P)
            _, rkA = A_.rref()
            assert rk == rkA, ('not a quadric', j, i)
            sol = {}
            for r in range(rk):
                piv = next(cc for cc in range(len(std2)) if int(R[r, cc]) != 0)
                sol[std2[piv]] = ratrec(int(R[r, len(std2)]))
            W[(j, i)] = {k: v for k, v in sol.items() if v != 0}
            print(f'  W_{j}{i} = ' + ' + '.join(f'{v}*X{a}X{b}' for (a, b), v in W[(j, i)].items()))
    json.dump({f'{j},{i}': [[list(k), str(v)] for k, v in W[(j, i)].items()] for (j, i) in W},
              open(os.path.join(HERE, 'flow_W.json'), 'w'))
    # symbolic H_jl
    Xs = sp.symbols('X0:9')
    Ys = sp.symbols('Y0:9')

    def law_expr(k, m):
        return sum(c * sp.prod([Xs[i] ** ex[i] for i in range(9)]) * sp.prod([Ys[i] ** ey[i] for i in range(9)])
                   for ex, ey, c in laws[(k, m)])
    Bexpr = Xs[1] * Ys[0] - Xs[0] * Ys[1] + Xs[2] * Ys[3] - Xs[3] * Ys[2]

    def Wexpr(j, i, V):
        return sum(v * V[a] * V[b] for (a, b), v in W[(j, i)].items()) if i > 0 else 0

    def Gop(F, j):
        return sp.expand(Ys[0] * sum(sp.diff(F, Xs[i]) * Wexpr(j, i, Xs) for i in range(1, 9)) -
                         Xs[0] * sum(sp.diff(F, Ys[i]) * Wexpr(j, i, Ys) for i in range(1, 9)))
    stats = []
    for j in (1, 2):
        GB = Gop(Bexpr, j)
        for l in range(9):
            Al = sp.expand(law_expr(l, 0))
            Gl = Gop(Al, j)
            nG, nGB, nA = len(sp.Add.make_args(Gl)), len(sp.Add.make_args(GB)), len(sp.Add.make_args(Al))
            # numeric check
            okc = 0
            for _ in range(5):
                cP, _ = chart_pt()
                cQ, _ = chart_pt()
                env = dict(zip(Xs, Xof(cP)))
                env.update(dict(zip(Ys, Xof(cQ))))
                H = (Bexpr * Gl - 3 * GB * Al)
                val = sp.Poly(H, *Xs, *Ys).eval(tuple(Xof(cP) + Xof(cQ)))
                val = int(val.p) * pow(int(val.q), -1, P) % P
                okc += (val == 0)
            # checker weight: products B*G_l and GB*A_l, scaled to integers
            def l1(e):
                return sum(abs(sp.Rational(cf)) for cf in sp.Poly(e, *Xs, *Ys).coeffs())
            stats.append((j, l, nG, nGB, nA, okc))
            print(f'  H_{j}{l}: G_{j}{l} {nG} terms (bideg (3,3)), G_B {nGB}, A_{l} {nA}; '
                  f'numeric zero at {okc}/5 random pairs; |G|_1 = {float(l1(Gl)):.3g}')
    return stats


if __name__ == '__main__':
    laws = load_laws()
    which = sys.argv[1] if len(sys.argv) > 1 else 'both'
    if which in ('1', 'both'):
        part1(laws)
    if which in ('2', 'both'):
        part2(laws)
