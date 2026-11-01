"""A0b step 1: Grant's P^8 model (3*Theta) of J = Jac(C), C : y^2 = f(x) = 4x^5 + c, c = 1, in Mumford coordinates.

Normalisation. Our curve y^5 = x(1-x) is u^2 = 1 - 4y^5 (u = 2x - 1); with x' = -y this is u^2 = 4x'^5 + 1, i.e. the
Baker/Grant normal form y^2 = 4x^5 + lambda_4 x^4 + ... + lambda_0 with lambda_0 = 1 and all other lambda_i = 0.
Everything below is over Z[1/2] (in fact over Z after scaling), no zeta_5 needed.

A point of J \\ Theta (Theta = image of C, through 0) is a Mumford pair (a, b):
    a = x^2 - s1 x + s2,  b = b1 x + b0,  a | f - b^2   (2 equations r1 = r0 = 0 in A^4: a complete intersection).
For D = P1 + P2 (Pi = (xi, yi)): s1 = x1 + x2, s2 = x1 x2, b(xi) = yi.

Kleinian functions (Baker), with du1 = sum dxi/yi, du2 = sum xi dxi/yi, d_j = d/du_j:
    p22 = s1, p12 = -s2, p11 = (F(x1,x2) - 2 y1 y2) / (4 (x1 - x2)^2), F the Kleinian 2-polar of f,
    pijk = d_k pij.  We check p222 = b1, p122 = b0 (so b(x) = p222 x + p122).
Grant's basis of L(3 Theta):  X = (1, p11, p12, p22, p111, p112, p122, p222, p12^2 - p11 p22).

This script
  (1) derives every pij, pijk as a polynomial in (s1, s2, b1, b0) modulo the Mumford relations (exact, sympy),
  (2) checks that each X_k has pole order <= 3 along Theta (Laurent expansion at P2 -> infinity, P1 generic),
  (3) writes model.json: the curve, the Mumford relations, and X_k as polynomials in (s1, s2, b1, b0).
Weights (for c = 0 homogeneous): wt x = 2, wt y = 5, wt s1 = 2, wt s2 = 4, wt b1 = 3, wt b0 = 5, wt c = 10.

Usage: python grant_model.py
"""
import itertools
import json
import sympy as sp

C0 = sp.Integer(1)          # lambda_0
x, x1, x2, y1, y2 = sp.symbols('x x1 x2 y1 y2')
s1, s2, b1, b0 = sp.symbols('s1 s2 b1 b0')
MUM = (s1, s2, b1, b0)
WT = {s1: 2, s2: 4, b1: 3, b0: 5}


def f(t):
    return 4 * t ** 5 + C0


lam = {0: C0, 1: 0, 2: 0, 3: 0, 4: 0, 5: 4}


def polarF(u, v):
    # Kleinian 2-polar: F(u,v) = sum_{i=0}^{2} (uv)^i [2 lam_{2i} + lam_{2i+1} (u + v)]
    return sum((u * v) ** i * (2 * lam[2 * i] + lam[2 * i + 1] * (u + v)) for i in range(3))


def mumford_relations():
    a = x ** 2 - s1 * x + s2
    b = b1 * x + b0
    r = sp.rem(sp.expand(f(x) - b ** 2), a, x)
    r = sp.Poly(r, x)
    r1 = sp.expand(r.coeff_monomial(x))
    r0 = sp.expand(r.coeff_monomial(1))
    return r1, r0


def reduce_y(expr):
    """Reduce a polynomial in x1,x2,y1,y2 modulo yi^2 = f(xi)."""
    p = sp.Poly(sp.expand(expr), y1, y2)
    out = 0
    for (e1, e2), co in p.terms():
        out += co * (f(x1) ** (e1 // 2)) * (f(x2) ** (e2 // 2)) * y1 ** (e1 % 2) * y2 ** (e2 % 2)
    return sp.expand(out)


# derivations d/du_j on functions of (x1, y1, x2, y2): dxi/du_j = (M^{-1})_{ij}
dx1 = {1: x2 * y1 / (x2 - x1), 2: -y1 / (x2 - x1)}
dx2 = {1: -x1 * y2 / (x2 - x1), 2: y2 / (x2 - x1)}


def D(j, h):
    dfx1 = sp.diff(f(x1), x1) / (2 * y1)  # dy1/dx1
    dfx2 = sp.diff(f(x2), x2) / (2 * y2)
    return (sp.diff(h, x1) + sp.diff(h, y1) * dfx1) * dx1[j] + (sp.diff(h, x2) + sp.diff(h, y2) * dfx2) * dx2[j]


def to_points(P):
    """Substitute Mumford coordinates by functions of the two points."""
    return P.subs({s1: x1 + x2, s2: x1 * x2, b1: (y1 - y2) / (x1 - x2), b0: (x1 * y2 - x2 * y1) / (x1 - x2)},
                  simultaneous=True)


def monos_upto(w):
    out = []
    for e in itertools.product(range(w // 2 + 1), range(w // 4 + 1), range(w // 3 + 1), range(w // 5 + 1)):
        if 2 * e[0] + 4 * e[1] + 3 * e[2] + 5 * e[3] <= w:
            out.append(s1 ** e[0] * s2 ** e[1] * b1 ** e[2] * b0 ** e[3])
    return out


def find_poly(h, w, K=8):
    """Find P(s1,s2,b1,b0) of weight <= w (monomials in a normal form w.r.t. the relations not enforced: we solve
    for any solution) with P = h on Sym^2 C."""
    monos = monos_upto(w)
    cs = sp.symbols(f'k0:{len(monos)}')
    P = sum(c * m for c, m in zip(cs, monos))
    num, den = sp.fraction(sp.together(h - to_points(P)))
    num = reduce_y(sp.expand(num))
    eqs = sp.Poly(num, x1, x2, y1, y2).coeffs()
    sol = sp.solve(eqs, cs, dict=True)
    assert sol, 'no solution'
    sol = sol[0]
    Psol = sp.expand(P.subs(sol).subs({c: 0 for c in cs}))
    return Psol


def laurent_pole_order(P, N=14):
    """Pole order along Theta: P1 generic, P2 -> infinity with local parameter z: x2 = z^-2, y2 = 2 z^-5 sqrt(1 + c z^10/4)."""
    z = sp.Symbol('z')
    y2s = 2 * z ** -5 * sp.series(sp.sqrt(1 + C0 * z ** 10 / 4), z, 0, N).removeO()
    e = to_points(P).subs({x2: z ** -2, y2: y2s})
    # multiply by z^k and find the smallest k making it regular
    e = sp.together(e)
    num, den = sp.fraction(e)
    num = sp.expand(num)
    den = sp.expand(den)
    on = min(m[0] for m in sp.Poly(num, z).monoms()) if num != 0 else 99
    # order of numerator / denominator at z = 0, with y1 treated formally (y1^2 = f(x1) not needed at leading order)
    od = min(m[0] for m in sp.Poly(den, z).monoms())
    # the leading coefficient might vanish on the curve: reduce it
    lead = sp.Poly(num, z).coeff_monomial(z ** on)
    lead = reduce_y(lead)
    k = on
    while lead == 0:
        k += 1
        lead = reduce_y(sp.Poly(num, z).coeff_monomial(z ** k))
    return od - k  # pole order (positive = pole)


def main():
    r1, r0 = mumford_relations()
    print('Mumford relations: r1 =', r1, '\n                   r0 =', r0)
    p22 = x1 + x2
    p12 = -x1 * x2
    p11 = (polarF(x1, x2) - 2 * y1 * y2) / (4 * (x1 - x2) ** 2)
    funcs = {}
    funcs['p22'] = (p22, 2)
    funcs['p12'] = (p12, 4)
    funcs['p11'] = (p11, 6)
    funcs['p222'] = (D(2, p22), 3)
    funcs['p122'] = (D(1, p22), 5)
    funcs['p112'] = (D(1, p12), 7)
    funcs['p111'] = (D(1, p11), 9)
    # consistency checks of the derivative formulas (symmetry of third derivatives)
    chk = [(D(2, p12), D(1, p22)), (D(2, p11), D(1, p12))]
    for u, v in chk:
        n, d = sp.fraction(sp.together(u - v))
        assert reduce_y(sp.expand(n)) == 0
    print('symmetry checks d2 p12 = d1 p22, d2 p11 = d1 p12: ok')
    polys = {}
    for name, (h, w) in funcs.items():
        P = find_poly(h, w)
        polys[name] = P
        print(f'{name:5s} = {P}')
    assert sp.expand(polys['p222'] - b1) == 0 and sp.expand(polys['p122'] - b0) == 0
    X = [sp.Integer(1), polys['p11'], polys['p12'], polys['p22'], polys['p111'], polys['p112'], polys['p122'],
         polys['p222'], sp.expand(polys['p12'] ** 2 - polys['p11'] * polys['p22'])]
    names = ['1', 'p11', 'p12', 'p22', 'p111', 'p112', 'p122', 'p222', 'p12^2-p11p22']
    # reduce X8 modulo the relations to low weight (Groebner normal form, grevlex)
    G = sp.groebner([r1, r0], *MUM, order='grevlex', domain='QQ')
    X = [sp.expand(G.reduce(sp.expand(Xi))[1]) for Xi in X]
    orders = []
    for nm, Xi in zip(names, X):
        po = laurent_pole_order(Xi)
        orders.append(po)
        print(f'X[{nm}] = {Xi}    pole order along Theta: {po}')
    assert all(o <= 3 for o in orders)
    # linear independence over Q: evaluate at random points of Sym^2 C (numerically exact over Q(y's) is enough:
    # use the polynomial representatives modulo the relations: rank of coefficient matrix after reduction)
    allm = sorted({m for Xi in X for m in sp.Poly(Xi, *MUM).monoms()})
    M = sp.Matrix([[sp.Poly(Xi, *MUM).coeff_monomial(m) for m in allm] for Xi in X])
    print('rank of the 9 normal forms (grevlex mod relations):', M.rank())
    out = {
        'curve': 'y^2 = 4x^5 + 1',
        'mumford_vars': ['s1', 's2', 'b1', 'b0'],
        'relations': [str(r1), str(r0)],
        'X_names': names,
        'X': [str(Xi) for Xi in X],
        'pole_orders': orders,
        'groebner_relations_grevlex': [str(g) for g in G.exprs],
    }
    with open('model.json', 'w') as fh:
        json.dump(out, fh, indent=1)
    print('wrote model.json')


if __name__ == '__main__':
    main()
