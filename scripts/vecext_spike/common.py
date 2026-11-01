"""Common definitions: the Weierstrass cubic, the two (2,2) addition laws of LSG/Elliptic/AdditionLaws.lean."""
import sympy as sp
from flint import fmpq_mat, fmpq

g2, g3 = sp.symbols('g2 g3')
x1, y1, x2, y2, t1, t2 = sp.symbols('x1 y1 x2 y2 t1 t2')
U1, V1, W1, U2, V2, W2 = sp.symbols('U1 V1 W1 U2 V2 W2')
T11, T31, T12, T32 = sp.symbols('T11 T31 T12 T32')  # T1 of P, T3 of P, T1 of Q, T3 of Q

def F(U, V, W):
    return V**2*W - 4*U**3 + g2*U*W**2 + g3*W**3

law1U = (-U1**2*W2**2*g2 - 2*U1*V1*V2*W2 - U1*V2**2*W1 - 3*U1*W1*W2**2*g3 + U2**2*W1**2*g2 + U2*V1**2*W2
    + 2*U2*V1*V2*W1 + 3*U2*W1**2*W2*g3)
law1V = (12*U1**2*U2*V2 - 12*U1*U2**2*V1 + U1*V1*W2**2*g2 - 2*U1*V2*W1*W2*g2 + 2*U2*V1*W1*W2*g2
    - U2*V2*W1**2*g2 + V1**2*V2*W2 - V1*V2**2*W1 + 3*V1*W1*W2**2*g3 - 3*V2*W1**2*W2*g3)
law1W = (-12*U1**2*U2*W2 + 12*U1*U2**2*W1 + U1*W1*W2**2*g2 - U2*W1**2*W2*g2 + V1**2*W2**2 - V2**2*W1**2)
law2U = (4*U1**2*V2*W2*g2 + 8*U1*U2*V1*W2*g2 + 8*U1*U2*V2*W1*g2 + 4*U1*V1*V2**2 + 12*U1*V1*W2**2*g3
    + 24*U1*V2*W1*W2*g3 + 4*U2**2*V1*W1*g2 + 4*U2*V1**2*V2 + 24*U2*V1*W1*W2*g3 + 12*U2*V2*W1**2*g3
    + V1*W1*W2**2*g2**2 + V2*W1**2*W2*g2**2)
law2V = (-48*U1**2*U2**2*g2 - 144*U1**2*U2*W2*g3 - 4*U1**2*W2**2*g2**2 - 144*U1*U2**2*W1*g3
    - 16*U1*U2*W1*W2*g2**2 - 12*U1*W1*W2**2*g2*g3 - 4*U2**2*W1**2*g2**2 - 12*U2*W1**2*W2*g2*g3
    + 4*V1**2*V2**2 + W1**2*W2**2*g2**3 - 36*W1**2*W2**2*g3**2)
law2W = (48*U1**2*U2*V2 + 48*U1*U2**2*V1 - 4*U1*V1*W2**2*g2 - 8*U1*V2*W1*W2*g2 - 8*U2*V1*W1*W2*g2
    - 4*U2*V2*W1**2*g2 + 4*V1**2*V2*W2 + 4*V1*V2**2*W1 - 12*V1*W1*W2**2*g3 - 12*V2*W1**2*W2*g3)

LAWS = {1: (law1U, law1V, law1W), 2: (law2U, law2V, law2W)}

AFF = {U1: x1, V1: y1, W1: 1, U2: x2, V2: y2, W2: 1}

def aff(p):
    return sp.expand(p.subs(AFF))

def fcub(x):
    return 4*x**3 - g2*x - g3

def nf(p):
    """Normal form modulo y_i^2 = 4x_i^3 - g2 x_i - g3 (y-degree <= 1)."""
    p = sp.expand(p)
    p = sp.rem(p, y1**2 - fcub(x1), y1)
    p = sp.rem(p, y2**2 - fcub(x2), y2)
    return sp.expand(p)

WT = {x1: 2, y1: 3, x2: 2, y2: 3, g2: 4, g3: 6, t1: 1, t2: 1}

def wdeg_set(p):
    P = sp.Poly(sp.expand(p), *WT.keys())
    gens = list(WT.keys())
    return {sum(e*WT[g] for e, g in zip(m, gens)) for m in P.monoms()}

def gmonos(w):
    """monomials g2^a g3^b of weight w"""
    out = []
    for a in range(w // 4 + 1):
        r = w - 4*a
        if r >= 0 and r % 6 == 0:
            out.append(g2**a * g3**(r // 6))
    return out

def solve_linear(unknown_terms, target, gens):
    """Find rationals r_j with sum r_j * unknown_terms[j] == target (as polynomials in gens).
    Returns list of r_j (one particular solution) or None."""
    rows = {}
    cols = len(unknown_terms)
    for j, term in enumerate(unknown_terms):
        P = sp.Poly(term, *gens)
        for m, c in P.terms():
            rows.setdefault(m, {})[j] = c
    Pt = sp.Poly(target, *gens)
    tdict = dict(Pt.terms())
    for m in tdict:
        rows.setdefault(m, {})
    mons = list(rows.keys())
    A = fmpq_mat(len(mons), cols + 1)
    for i, m in enumerate(mons):
        for j, c in rows[m].items():
            A[i, j] = fmpq(int(sp.numer(c)), int(sp.denom(c)))
        c = tdict.get(m, 0)
        c = sp.Rational(c)
        A[i, cols] = fmpq(int(c.p), int(c.q))
    R, rank = A.rref()
    # check consistency: no pivot in last column
    sol = [fmpq(0)] * cols
    for i in range(rank):
        # find pivot column
        piv = None
        for j in range(cols + 1):
            if R[i, j] != 0:
                piv = j
                break
        if piv == cols:
            return None
        sol[piv] = R[i, cols]
    return [sp.Rational(int(s.p), int(s.q)) for s in sol]
