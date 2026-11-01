"""Cross-check against the literature (Coble 1917, Barth 1995): the 9 quadrics of the 3Theta-embedded Jacobian are the
partial derivatives of a cubic (the Coble cubic).  Exact over Q: find all cubics C with dC/dX_i in span(Q) for all i.
Usage: python coble_check.py
"""
import itertools, json
import sympy as sp
X = sp.symbols('X0:9')
quads = [sum(c * X[m[0]] * X[m[1]] for m, c in q) for q in json.load(open('ideal.json'))['quadrics']]
m3 = list(itertools.combinations_with_replacement(range(9), 3))
cs = sp.symbols(f'c0:{len(m3)}')
C = sum(c * X[a] * X[b] * X[d] for c, (a, b, d) in zip(cs, m3))
ls = sp.symbols('l0:81')
eqs = []
for i in range(9):
    expr = sp.expand(sp.diff(C, X[i]) - sum(ls[9 * i + j] * quads[j] for j in range(9)))
    eqs += sp.Poly(expr, *X).coeffs()
sol = sp.linsolve(eqs, list(cs) + list(ls))
sol = list(sol)[0]
free = sorted(set().union(*[s.free_symbols for s in sol]), key=str)
print('dimension of the space of such cubics:', len(free))
Csol = sp.expand(C.subs(dict(zip(list(cs) + list(ls), sol))))
for f in free:
    Cf = sp.expand(sp.diff(Csol, f))
    grads = [sp.Poly(sp.diff(Cf, X[i]), *X) for i in range(9)]
    M = sp.Matrix([[g.coeff_monomial(X[a] * X[b]) for (a, b) in itertools.combinations_with_replacement(range(9), 2)] for g in grads])
    print('cubic:', Cf)
    print('rank of span of its 9 partials:', M.rank())
