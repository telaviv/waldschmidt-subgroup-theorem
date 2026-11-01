"""A0b step 9: exact symmetry identities of the (2,2) laws (cheap; used by the semantic completeness argument).
  (S1) [-1]-transpose:  A_k^{(m)}(X, [-1]Y) = eps_{km} A_m^{(k)}(X, Y)  exactly (as standard-monomial representatives),
       [-1] = diag(1,1,1,1,-1,-1,-1,-1,1).  (A_k^{(m)} ~ X_k(x+y) X_m(x-y): swapping y -> -y swaps x+y and x-y.)
  (S2) swap:  A_k^{(m)}(Y, X) = eps'_{m} A_k^{(m)}(X, Y)  modulo (Q(X)) + (Q(Y)) (here checked as exact equality of
       representatives after re-normalising; the representative basis is symmetric in X, Y).
Usage: python symmetry_checks.py
"""
import json
from fractions import Fraction
lq = json.load(open('laws_Q.json'))
NEG = [1, 1, 1, 1, -1, -1, -1, -1, 1]
L = {}
for key, terms in lq['laws'].items():
    k, m = map(int, key.split(','))
    L[(k, m)] = {tuple(e): Fraction(c) for e, c in terms}
def negY(P):
    out = {}
    for e, c in P.items():
        s = 1
        for i in range(9):
            if NEG[i] == -1 and e[9 + i] % 2:
                s = -s
        out[e] = s * c
    return out
def swap(P):
    return {tuple(list(e[9:]) + list(e[:9])): c for e, c in P.items()}
def ratio(P, Q):
    if set(P) != set(Q):
        return None
    r = None
    for e in P:
        q = P[e] / Q[e]
        if r is None:
            r = q
        elif q != r:
            return None
    return r
s1 = {}
for k in range(9):
    for m in range(9):
        s1[(k, m)] = ratio(negY(L[(k, m)]), L[(m, k)])
print('(S1) A_k^(m)(X,[-1]Y) = eps A_m^(k)(X,Y): all exact:', all(v is not None for v in s1.values()),
      ' eps values:', sorted({str(v) for v in s1.values()}))
s2 = {}
for k in range(9):
    for m in range(9):
        s2[(k, m)] = ratio(swap(L[(k, m)]), L[(k, m)])
print('(S2) A_k^(m)(Y,X) = eps A_k^(m)(X,Y): exact for', sum(v is not None for v in s2.values()), 'of 81;',
      'eps values:', sorted({str(v) for v in s2.values() if v is not None}))
