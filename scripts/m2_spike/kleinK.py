"""M2 spike (untrusted, exact sympy): Lemma K-natural, i.e. d_i d_j log theta_0 = -3 p_ij + c_ij.

theta_0 is the X_0-coordinate of the lift (X_0 = 1 on the Mumford chart, so div theta_0 = 3 Theta).  Near Theta we use
chart k (X_k != 0, k = 4 or 8): theta_0 = theta_k * V_0, V = X/X_k.  The claim is equivalent to the regularity on the
chart {X_k != 0} of
        q_k := d_i d_j log (X_0/X_k) + kappa * X_m/X_0         (kappa = 3, X_m = p_ij: m(11)=1, m(12)=2, m(22)=3).
On the Mumford chart (X_0 = 1, derivations d_j X_l = W0_{jl}(X) from flow_W.json) q_k = -d_i d_j log X_k + kappa X_m.
Sufficient test: F := q_k * X_k^2 = -(d_i d_j X_k) X_k + d_i X_k d_j X_k + kappa X_m X_k^2 is (the restriction of) a
quadric in X, i.e. lies in eval(S_2) modulo the Mumford relations.  Then q_k = Q(X)/X_k^2 is regular where X_k != 0,
and q_4 = Q/X_4^2 also gives the fibre flow of tau_4 = T_4/X_4 (tau_4' = q/3).

We solve for kappa (linear) and report the quadric Q (coefficients) per (i, j) and chart.
"""
import json, itertools, os, sys
import sympy as sp

HERE = os.path.dirname(os.path.abspath(__file__))
AB = os.path.join(HERE, '..', 'abvar_spike')
JAC = os.path.join(HERE, '..', 'jac')
m = json.load(open(os.path.join(AB, 'model.json')))
s1, s2, b1, b0 = sp.symbols('s1 s2 b1 b0')
env = {'s1': s1, 's2': s2, 'b1': b1, 'b0': b0}
Xm = [sp.sympify(e, locals=env) for e in m['X']]
G = sp.groebner([sp.sympify(e, locals=env) for e in m['relations']], s1, s2, b1, b0, order='grevlex', domain='QQ')
W0 = json.load(open(os.path.join(JAC, 'flow_W.json')))

Xs = sp.symbols('X0:9')
def Wpoly(j, l):
    if l == 0:
        return sp.Integer(0)
    return sum(sp.Rational(c) * Xs[a] * Xs[b] for (a, b), c in W0[f'{j},{l}'])

def D(j, expr):
    """chart-0 derivation d/du_j on polynomials in X (X0 = 1 constant)."""
    return sp.expand(sum(sp.diff(expr, Xs[l]) * Wpoly(j, l) for l in range(1, 9)))

def ev(expr):
    e = sp.expand(expr.subs({Xs[k]: Xm[k] for k in range(9)}))
    return G.reduce(e)[1]

# eval(S_2): normal forms of X_a X_b
quad = list(itertools.combinations_with_replacement(range(9), 2))
quadNF = [ev(Xs[a] * Xs[b]) for a, b in quad]
mons = set()
for e in quadNF:
    mons |= set(sp.Poly(e, s1, s2, b1, b0).monoms())

kappa = sp.Symbol('kappa')
mi = {(1, 1): 1, (1, 2): 2, (2, 1): 2, (2, 2): 3}
res = {}
for k in (4, 8):
    for (i, j) in [(1, 1), (1, 2), (2, 2)]:
        Xk = Xs[k]
        F0 = -D(i, D(j, Xk)) * Xk + D(i, Xk) * D(j, Xk)
        F1 = Xs[mi[(i, j)]] * Xk**2
        FN = ev(F0.subs(Xs[0], 1)) + kappa * ev(F1.subs(Xs[0], 1))
        cs = sp.symbols(f'c0:{len(quad)}')
        diff = sp.expand(FN - sum(c * q for c, q in zip(cs, quadNF)))
        eqs = sp.Poly(diff, s1, s2, b1, b0).coeffs()
        sol = sp.solve(eqs, list(cs) + [kappa], dict=True)
        if not sol:
            print(f'chart {k}, (i,j)=({i},{j}): NOT a quadric for any kappa')
            res[f'{k},{i},{j}'] = None
            continue
        s = sol[0]
        kap = s.get(kappa, 'free')
        Q = sp.expand(sum(s.get(c, c) * Xs[a] * Xs[b] for c, (a, b) in zip(cs, quad)))
        Q = Q.subs({c: 0 for c in cs})   # free parameters = elements of I_2; set to 0
        print(f'chart {k}, (i,j)=({i},{j}): kappa = {kap};  Q = {Q}')
        res[f'{k},{i},{j}'] = {'kappa': str(kap), 'Q': str(Q)}
json.dump(res, open(os.path.join(HERE, 'kleinK.json'), 'w'), indent=1)
