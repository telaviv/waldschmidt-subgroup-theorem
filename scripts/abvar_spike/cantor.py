"""ABVAR spike: size of the generic group law of J(C) in Mumford coordinates (the affine chart J \\ Theta),
C : y^2 = f(x) = x^(2g+1) + 1 (over Qbar this is y^5 = x(1-x) for g = 2 and y^7 = x(1-x) for g = 3:
put u = 2x - 1, then u^2 = 1 - 4y^N, and rescale y by 4^(-1/N)).

A point of J \\ Theta is (a, b): a = x^g + a_{g-1} x^{g-1} + ... + a_0, b = b_{g-1} x^{g-1} + ... + b_0 with
a | f - b^2 (g equations: the affine chart is a complete intersection of dimension g in A^{2g}).
Generic sum (gcd(a, a') = 1, Cantor composition without reduction steps beyond one):
  c = CRT(b mod a, b' mod a')            (degree < 2g)
  a'' = monic((f - c^2) / (a a'))        (degree <= 2g - 1 ... reduce until deg <= g)
  b'' = -c mod a''
We report the number of monomials in the numerators of the coordinates of the sum, as rational functions in the
4g coordinates (no reduction modulo the curve relations), and the denominator degrees.

Usage: python cantor.py [g]    (g = 2 default; g = 3 takes a few minutes)
"""
import sys
import time
import sympy as sp


def setup(g):
    x = sp.Symbol('x')
    A = sp.symbols(f'a0:{g}')
    B = sp.symbols(f'b0:{g}')
    A2 = sp.symbols(f"c0:{g}")
    B2 = sp.symbols(f"d0:{g}")
    a = x ** g + sum(A[i] * x ** i for i in range(g))
    b = sum(B[i] * x ** i for i in range(g))
    a2 = x ** g + sum(A2[i] * x ** i for i in range(g))
    b2 = sum(B2[i] * x ** i for i in range(g))
    f = x ** (2 * g + 1) + 1
    return x, (A, B, A2, B2), a, b, a2, b2, f


def cantor_generic(g):
    """Generic Cantor sum over the fraction field K = Q(a, b, a', b') of the 4g coordinates.

    The divisions (f - c^2)/(a a') are exact only modulo the curve relations a | f - b^2, a' | f - b'^2; we take the
    polynomial quotient (the remainder lies in the ideal of the relations), which is a valid formula on J x J.
    Returns, for each coordinate of the sum, (name, #numerator terms, #denominator terms, deg num, deg den)."""
    x, (A, B, A2, B2), a, b, a2, b2, f = setup(g)
    gens = list(A) + list(B) + list(A2) + list(B2)
    K = sp.QQ.frac_field(*gens)
    P = lambda e: sp.Poly(e, x, domain=K)
    t0 = time.time()
    pa, pa2, pb, pb2, pf = P(a), P(a2), P(b), P(b2), P(f)
    s, t, h = pa.gcdex(pa2)                       # s*a + t*a2 = h, h in K
    k = ((pb2 - pb) * s).rem(pa2)
    c = pb + pa * k * P(1 / h.as_expr()) if False else pb + pa * k.quo(h)
    ua = pa * pa2
    steps = 0
    while True:
        q = (pf - c * c).quo(ua)                  # exact modulo the relations
        steps += 1
        q = q.monic()
        c = (-c).rem(q)
        if q.degree() <= g:
            break
        ua = q
    print(f"  {steps} composition/reduction step(s), {time.time() - t0:.1f}s")
    out = []
    for name, poly in (("a", q), ("b", c)):
        coeffs = list(reversed(poly.all_coeffs()))
        for i, co in enumerate(coeffs):
            if name == "a" and i == g:
                continue
            e = K.to_sympy(co) if hasattr(K, "to_sympy") else co
            n, d = sp.fraction(sp.cancel(e))
            out.append((f"{name}{i}''", len(sp.Add.make_args(sp.expand(n))), len(sp.Add.make_args(sp.expand(d))),
                        sp.Poly(n, *gens).total_degree(), sp.Poly(d, *gens).total_degree()))
    print(f"  total {time.time() - t0:.1f}s")
    return out


if __name__ == "__main__":
    g = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    print(f"genus {g}: f = x^{2*g+1} + 1")
    _, _, a, _, a2, _, _ = setup(g)
    x = sp.Symbol('x')
    res = sp.resultant(a, a2, x)
    print(f"  resultant(a, a') (the CRT denominator): {len(sp.Add.make_args(sp.expand(res)))} terms")
    for row in cantor_generic(g):
        print("  %-5s numerator %6d terms (deg %3d), denominator %6d terms (deg %3d)" % (row[0], row[1], row[3], row[2], row[4]))
