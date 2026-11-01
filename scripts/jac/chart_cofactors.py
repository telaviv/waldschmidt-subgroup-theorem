"""Cofactors for 'Grant's map lands in V(Q)' and the Mumford remainder (UNTRUSTED; Lean re-checks by ring)."""
import sympy as sp
s1, s2, b1, b0, x = sp.symbols('s1 s2 b1 b0 x')
X = [sp.Integer(1), b1**2/4 - s1**3 + s1*s2, -s2, s1, -2*b0*s1**2 + b0*s2 - b1**3/4 + b1*s1**3 - 3*b1*s1*s2,
     -b0*s1 - b1*s2, b0, b1, b0*b1/2 + 2*s1**2*s2]
r1 = -2*b0*b1 - b1**2*s1 + 4*s1**4 - 12*s1**2*s2 + 4*s2**2
r0 = -b0**2 + b1**2*s2 - 4*s1**3*s2 + 8*s1*s2**2 + 1
Q = [lambda X: -X[0]*X[8] - X[1]*X[3] + X[2]**2,
     lambda X: X[0]*X[7] - 2*X[1]*X[5] + 2*X[2]*X[4],
     lambda X: -2*X[1]*X[6] + X[2]*X[5] + X[3]*X[4],
     lambda X: -X[0]*X[4] - X[1]*X[7] - X[2]*X[6] + 2*X[3]*X[5],
     lambda X: X[0]*X[5] - X[2]*X[7] + X[3]*X[6],
     lambda X: -X[0]*X[2] - 2*X[1]*X[8] - 3*X[3]**2 - X[4]*X[6] + X[5]**2,
     lambda X: X[0]*X[3] - 4*X[1]**2 - 4*X[2]*X[8] - X[4]*X[7] + X[5]*X[6],
     lambda X: -X[0]**2 + 8*X[1]*X[2] - 2*X[3]*X[8] - X[5]*X[7] + X[6]**2,
     lambda X: 8*X[0]*X[1] + 4*X[2]*X[3] + 4*X[4]*X[5] - X[7]**2 + 4*X[8]**2]
for j, q in enumerate(Q):
    e = sp.expand(q(X))
    if e == 0:
        print(j, 'identically zero'); continue
    # ansatz: c1, c0 of total degree <= 4
    mons = [m for m in sp.itermonomials([s1, s2, b1, b0], 4)]
    cs = sp.symbols(f'u0:{2*len(mons)}')
    C1 = sum(cs[i] * mons[i] for i in range(len(mons)))
    C0 = sum(cs[len(mons) + i] * mons[i] for i in range(len(mons)))
    eq = sp.Poly(sp.expand(e - C1 * r1 - C0 * r0), s1, s2, b1, b0)
    sol = sp.solve(eq.coeffs(), cs, dict=True)
    assert sol, j
    sol = sol[0]
    c1 = sp.expand(C1.subs(sol).subs({c: 0 for c in cs}))
    c0 = sp.expand(C0.subs(sol).subs({c: 0 for c in cs}))
    assert sp.expand(e - c1 * r1 - c0 * r0) == 0
    print(j, 'c1 =', sp.factor(c1), '| c0 =', sp.factor(c0))
a = x**2 - s1*x + s2
bb = b1*x + b0
f = 4*x**5 + 1
qq, rr = sp.div(sp.expand(f - bb**2), a, x)
print('quotient', sp.expand(qq))
print('remainder', sp.collect(sp.expand(rr), x))
