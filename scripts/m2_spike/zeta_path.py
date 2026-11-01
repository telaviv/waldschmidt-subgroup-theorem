"""M2 spike (untrusted): the second-kind period along a moving divisor P + Q0 on y^2 = 4x^5 + 1.

If zeta1 has d zeta1 / d u_j = -p1j (Kleinian, du1 = dx/y, du2 = x dx/y), then along D = P + Q0 (Q0 fixed)
    d zeta1 = -(p11(D) + x p12(D)) dx/y,
with p11 = b1^2/4 - s1^3 + s1 s2, p12 = -s2 (model.json), s1 = x + x0, s2 = x x0, b1 = (y - y0)/(x - x0).
We look for a constant c and a rational R(x, y) (Q0 = (x0, y0) symbolic) with
    (p11 + x p12) dx/y = c x^3 dx/y + dR      on the curve,
so that the fibre period of the closed path is eta1(gamma) = -c * int_gamma x^3 dx/y  (exact form integrates to 0).
"""
import sympy as sp

x, y, x0, y0 = sp.symbols('x y x0 y0')
f = 4 * x**5 + 1
f0 = 4 * x0**5 + 1
s1, s2 = x + x0, x * x0
b1 = (y - y0) / (x - x0)
p11 = b1**2 / 4 - s1**3 + s1 * s2
p12 = -s2
lhs = (p11 + x * p12) / y            # coefficient of dx

def ddx(R):
    """d/dx along the curve (dy/dx = f'(x)/(2y))."""
    return sp.diff(R, x) + sp.diff(R, y) * sp.diff(f, x) / (2 * y)

def red(e):
    """Normal form: reduce y^2 -> f, y0^2 -> f0 in the numerator, then test for zero."""
    e = sp.together(sp.expand(e))
    n, d = sp.fraction(e)
    n = sp.expand(n)
    n = sp.Poly(n, y, y0)
    out = 0
    for (a, b), c in n.terms():
        out += c * f**(a // 2) * y**(a % 2) * f0**(b // 2) * y0**(b % 2)
    return sp.simplify(sp.expand(out)), d

c = sp.Symbol('c')
# ansatz: R = (alpha*y + beta*y0) / (x - x0)
al, be = sp.symbols('al be')
R = (al * y + be * y0) / (x - x0)
expr = lhs - c * x**3 / y - ddx(R)
num, den = red(expr)
num = sp.expand(num)
coeffs = sp.Poly(num, x, y, y0, x0).coeffs()
sol = sp.solve(coeffs, [al, be, c], dict=True)
print("solutions:", sol)
for s in sol:
    chk, _ = red(expr.subs(s))
    print("residual:", sp.simplify(chk))
