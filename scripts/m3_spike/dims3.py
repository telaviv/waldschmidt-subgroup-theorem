"""M3 spike (untrusted, arithmetic only): size table for a genus-3 3Theta model in P^26 versus Grant's P^8.

Assumes projective normality (Koizumi) and h^0(k*3Theta) = (3k)^g, i.e. dim (S/I)_d = 27 d^3 (g = 3) and 9 d^2 (g = 2).
mu_{2N}-weight sparsity factor w = 2N (10 for N = 5, 14 for N = 7) is applied as a rough divisor (A0.2 measured
~1/10 for genus 2).
"""
from math import comb


def table(g, nvar, w, dmax=12):
    print(f"genus {g}: {nvar} coordinates, weight factor ~{w}")
    print(f"  {'d':>3} {'#monomials S_d':>16} {'dim (S/I)_d':>12} {'dim I_d':>14} {'(S/I)_d / w':>12}")
    for d in range(1, dmax + 1):
        S = comb(nvar + d - 1, d)
        Q = (3 * d) ** g
        print(f"  {d:>3} {S:>16} {Q:>12} {S - Q:>14} {Q // w:>12}")
    q2 = comb(nvar + 1, 2) - 6 ** g
    print(f"  quadrics in I_2: {q2};  Sym^2 = {comb(nvar + 1, 2)} vs h0(6Theta) = {6 ** g}")
    # one (2,2) law: nvar coordinates, each in (S/I)_2 (x) (S/I)_2
    print(f"  one (2,2) law: {nvar} x {6 ** g}^2 = {nvar * 36 ** g} nominal coefficients (~{nvar * 36 ** g // w} weighted)")
    print(f"  Dup (degree 4): {nvar} x {12 ** g} = {nvar * 12 ** g} nominal (~{nvar * 12 ** g // w} weighted)")
    print(f"  Fourier: Pf(3E_Theta) = {3 ** g}, Pf(6E_Theta) = dim T(L^2) = {6 ** g}")
    print()


table(2, 9, 10)
table(3, 27, 14)

# rough single-copy identity costs (number of expanded products), genus 3, weight factor 14
w = 14
dupT = 27 * 12 ** 3 // w // 27          # terms per Dup coordinate (~123)
qT = 10                                  # terms per quadric (guess, as in genus 2)
print("genus-3 single-copy certificate scale (expanded products, rough):")
print(f"  terms per Dup coordinate ~ {dupT}")
print(f"  dup_onQ  Q_i(Dup(X)) mod I_8: 162 identities x {qT}*{dupT}^2 = {162 * qT * dupT ** 2:.2e} products")
WT = 27 * 30                             # chart field: 27 components x ~30 quadratic terms (genus 2: 27-51 terms)
print(f"  E2 (dup transports one chart field), degree 9: 3 x 27 identities x ~{dupT}*{WT}*{dupT // 4} = "
      f"{81 * dupT * WT * (dupT // 4):.2e}")
for N in (7, 8, 9, 10):
    cof = (3 * (N - 4)) ** 3 // w
    print(f"  P2 at degree N = {N}: cofactor space {27}x(S/I)_{N-4}/w = {27 * cof}, "
          f"products per identity ~{27 * cof * dupT:.2e}, (S/I)_N = {(3 * N) ** 3}")
print()
print("genus-2 reference (A0/A4, measured): P2 at degree 7, (S/I)_7 = 441; V2' 64 identities x ~1.2e4 term-pairs;")
print("kernel throughput ~0.8 ms per innermost term-product (A0.3 item 5).")
