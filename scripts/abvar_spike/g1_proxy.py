"""A0b step 10 (proxy for the chart comparison G1): size of law 0 pulled back to the Mumford chart x Mumford chart,
A_k^{(0)}(X(D), X(D')) as polynomials in (s1,s2,b1,b0, s1',s2',b1',b0') (no reduction modulo the chart relations),
and of B(X(D),X(D'))^3 = A_0^{(0)}.  [Numerical size measurement only.]
"""
import json
import flint
from jac import load_model
m = load_model()
names = ('s1', 's2', 'b1', 'b0', 't1', 't2', 'c1', 'c0')
ctx = flint.fmpq_mpoly_ctx.get(names, 'degrevlex')
g = ctx.gens()
envD = dict(zip(['s1', 's2', 'b1', 'b0'], g[:4]))
envE = dict(zip(['s1', 's2', 'b1', 'b0'], g[4:]))
one = ctx.from_dict({tuple([0] * 8): 1})
XD = [one if e == '1' else eval(e.replace('^', '**'), {}, envD) for e in m['X']]
XE = [one if e == '1' else eval(e.replace('^', '**'), {}, envE) for e in m['X']]
lq = json.load(open('laws_Q.json'))
tot = 0
for k in range(9):
    P = ctx.from_dict({})
    for e, c in lq['laws'][f'{k},0']:
        num, den = (c.split('/') + ['1'])[:2]
        t = one * flint.fmpq(int(num), int(den))
        for i in range(9):
            for _ in range(e[i]):
                t = t * XD[i]
            for _ in range(e[9 + i]):
                t = t * XE[i]
        P = P + t
    n = len(P.monoms())
    tot += n
    print(f'A_{k}^(0)(X(D),X(D\')) : {n} terms, total degree {P.total_degree()}')
print('total', tot)
