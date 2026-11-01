"""ABVAR spike: dimension counts for projective models of a principally polarised abelian variety J of dim g
embedded by k*Theta (k >= 3: very ample by Lefschetz, projectively normal by Koizumi), and the sizes of the
objects a Stage-2-style multiplicity estimate would have to certify in Lean.

Facts used (standard, [Lit]): h^0(J, k*Theta) = k^g (Riemann-Roch for a principal polarisation);
projective normality => H(R/I, d) = h^0(d*k*Theta) = (d*k)^g for all d >= 1 (Hilbert function of the cone).
Addition laws of bidegree (2,2) (Lange-Ruppert 1985, symmetric L): each law is an (N+1)-tuple of
bihomogeneous forms, determined modulo (I(P), I(Q)) by an element of H^0(2kTheta) (x) H^0(2kTheta) per coordinate.

Usage: python dims.py
"""
from math import comb


def row(g, k):
    n1 = k ** g                  # number of projective coordinates, N + 1
    sym2 = comb(n1 + 1, 2)       # quadratic monomials
    h2 = (2 * k) ** g            # H(R/I, 2)
    quadrics = sym2 - h2         # independent quadrics in I_2
    law_coeffs = n1 * h2 * h2    # one (2,2) law modulo (I(P), I(Q)): N+1 coordinates in R_2 (x) R_2
    h4 = (4 * k) ** g            # H(R/I, 4): one identity F(A(P,Q)) lives in bidegree (4,4)
    ident_space = h4 * h4        # size of the normal-form space of one identity F_j(A(P,Q)) mod (I(P), I(Q))
    return dict(g=g, k=k, N=n1 - 1, quadrics=quadrics, law_coeffs=law_coeffs, ident_space=ident_space)


if __name__ == "__main__":
    print(f"{'g':>2} {'k':>2} {'P^N':>6} {'#quadrics':>10} {'(2,2)-law coeffs':>17} {'(4,4) normal forms':>19}")
    for g, k in [(1, 3), (2, 3), (2, 4), (3, 3), (3, 4)]:
        r = row(g, k)
        print(f"{r['g']:>2} {r['k']:>2} {('P^%d' % r['N']):>6} {r['quadrics']:>10} {r['law_coeffs']:>17} {r['ident_space']:>19}")
    print()
    print("sanity: (g,k) = (1,3) gives the plane cubic (0 quadrics); (2,4) gives Flynn's 72 quadrics in P^15.")
