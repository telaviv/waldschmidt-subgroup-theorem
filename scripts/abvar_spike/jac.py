"""Shared helpers for the A0b spike: the P^8 model of J = Jac(y^2 = 4x^5 + 1) (model.json from grant_model.py),
Cantor arithmetic over F_p, and evaluation of the 9 coordinates X_k at Mumford points.

Coordinates: X = (1, p11, p12, p22, p111, p112, p122, p222, p12^2 - p11 p22) as polynomials in the Mumford
coordinates (s1, s2, b1, b0) of a = x^2 - s1 x + s2, b = b1 x + b0.
"""
import json
import os
import random
import itertools
import flint

HERE = os.path.dirname(os.path.abspath(__file__))


def load_model():
    with open(os.path.join(HERE, 'model.json')) as fh:
        return json.load(fh)


# ------------------------------------------------------------------ model as fmpq_mpoly in s1,s2,b1,b0
def model_polys():
    m = load_model()
    ctx = flint.fmpq_mpoly_ctx.get(('s1', 's2', 'b1', 'b0'), 'degrevlex')
    s1, s2, b1, b0 = ctx.gens()
    env = {'s1': s1, 's2': s2, 'b1': b1, 'b0': b0}
    X = [eval(e.replace('^', '**'), {}, env) if e != '1' else ctx.from_dict({(0, 0, 0, 0): 1}) for e in m['X']]
    X = [ctx.from_dict({(0, 0, 0, 0): 1}) + 0 * s1 if isinstance(Xi, int) else Xi for Xi in X]
    rel = [eval(e.replace('^', '**'), {}, env) for e in m['relations']]
    return ctx, X, rel


# ------------------------------------------------------------------ F_p arithmetic
class Fp:
    def __init__(self, p):
        self.p = p
        self.R = lambda coeffs: flint.nmod_poly(coeffs, p)
        self.f = flint.nmod_poly([1, 0, 0, 0, 0, 4], p)   # 4x^5 + 1
        self.g = 2

    def poly(self, coeffs):
        return flint.nmod_poly(coeffs, self.p)

    def monic(self, a):
        lc = a.coeffs()[-1]
        return a * flint.nmod(lc, self.p) ** -1

    def random_point_on_curve(self):
        p = self.p
        while True:
            xx = random.randrange(p)
            v = int(self.f(xx))
            if v == 0:
                continue
            if pow(v, (p - 1) // 2, p) == 1:
                yy = sqrt_mod(v, p)
                return xx, yy

    def divisor_from_points(self, pts):
        """Mumford rep of sum (xi, yi) - n*inf for distinct x's."""
        a = self.poly([1])
        for (xx, _) in pts:
            a = a * self.poly([-xx % self.p, 1])
        # b by Lagrange interpolation
        b = self.poly([0])
        for i, (xi, yi) in enumerate(pts):
            li = self.poly([1])
            den = 1
            for j, (xj, _) in enumerate(pts):
                if j != i:
                    li = li * self.poly([-xj % self.p, 1])
                    den = den * (xi - xj) % self.p
            b = b + li * (yi * pow(den, -1, self.p) % self.p)
        return (a, b)

    def random_divisor(self):
        pts = []
        while len(pts) < 2:
            P = self.random_point_on_curve()
            if all(P[0] != Q[0] for Q in pts):
                pts.append(P)
        return self.divisor_from_points(pts)

    def random_theta_point(self):
        return self.divisor_from_points([self.random_point_on_curve()])

    def add(self, D1, D2):
        a1, b1 = D1
        a2, b2 = D2
        d0, e1, e2 = xgcd(a1, a2, self)
        d, c1, c2 = xgcd(d0, b1 + b2, self)
        s1 = c1 * e1
        s2 = c1 * e2
        s3 = c2
        a = (a1 * a2) // (d * d)
        b = ((s1 * a1 * b2 + s2 * a2 * b1 + s3 * (b1 * b2 + self.f)) // d) % a
        a = self.monic(a)
        while a.degree() > self.g:
            a = (self.f - b * b) // a
            a = self.monic(a)
            b = (-b) % a
        return (a, b % a if a.degree() > 0 else self.poly([0]))

    def neg(self, D):
        a, b = D
        return (a, -b)

    def mumford_coords(self, D):
        a, b = D
        assert a.degree() == 2, 'divisor on Theta'
        c = a.coeffs()
        bc = b.coeffs() + [0, 0]
        # a = x^2 - s1 x + s2
        return (-int(c[1]) % self.p, int(c[0]), int(bc[1]), int(bc[0]))


def xgcd(a, b, F):
    """Monic gcd d = u a + v b over F_p."""
    p = F.p
    r0, r1 = a, b
    s0, s1 = F.poly([1]), F.poly([0])
    t0, t1 = F.poly([0]), F.poly([1])
    while r1 != 0:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
        t0, t1 = t1, t0 - q * t1
    if r0 == 0:
        return r0, s0, t0
    lc = flint.nmod(r0.coeffs()[-1], p) ** -1
    return r0 * lc, s0 * lc, t0 * lc


def sqrt_mod(a, p):
    # Tonelli-Shanks
    a %= p
    if a == 0:
        return 0
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
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
        bb = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, bb * bb % p, t * bb * bb % p, r * bb % p
    return r


# ------------------------------------------------------------------ evaluating X at a Mumford point mod p
def X_eval_fn(p):
    ctx, X, rel = model_polys()

    def ev(mc):
        vals = [flint.nmod(v, p) for v in mc]
        out = []
        for Xi in X:
            acc = flint.nmod(0, p)
            for exps, co in zip(Xi.monoms(), Xi.coeffs()):
                t = flint.nmod(int(co.p), p) / flint.nmod(int(co.q), p)
                for v, e in zip(vals, exps):
                    if e:
                        t = t * v ** e
                acc += t
            out.append(int(acc))
        return out
    return ev


def quad_monos(n=9, d=2):
    return list(itertools.combinations_with_replacement(range(n), d))
