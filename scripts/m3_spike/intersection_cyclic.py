"""M3 spike (untrusted, numerical): is Z[zeta]*gamma the full H_1 of C_N : y^N = x(1-x)?

Model u^2 = 1 - 4 y^N (u = 2x - 1), genus g = (N-1)/2, one point at infinity.
Differentials w_s = y^s dy/u, s = 0..N-2 (first kind s < g, second kind s >= g, no residues).
Cycles c_e = [zeta^e] gamma, gamma = l - [zeta] l, l the lift of x in [0,1] with y > 0, e = 0..N-2.

Periods: int_{c_e} w_s = zeta^{(s+1)e} (1 - zeta^{s+1}) * (-1/N) B((s+1)/N, (s+1)/N).
Riemann bilinear relation for second-kind differentials:
   sum_i (A_i(phi) B_i(psi) - B_i(phi) A_i(psi)) = 2 pi i sum_P Res_P(psi * int phi).
With the period matrix P (rows: cycles, columns: differentials) and the intersection matrix J of the c_e,
   Pair = P^T J^{-1} P  (up to a global sign / transpose convention),
so J^{-1} = P^{-T} Pair P^{-1}.  Local parameter at infinity: y = t^-2, u = 2i t^-N sqrt(1 - t^{2N}/4):
   w_s = i t^{N-3-2s} (1 + O(t^{2N})) dt,  Res(w_b int w_a) = -1/(N-2-2a) if a+b = N-2, else 0.

Output: J (should be an integral antisymmetric matrix); |det J| = [H_1 : Z[zeta]gamma]^2.
"""
import mpmath as mp

mp.mp.dps = 60


def run(N):
    g = (N - 1) // 2
    n = N - 1
    z = mp.exp(2j * mp.pi / N)
    P = mp.matrix(n, n)
    for e in range(n):
        for s in range(n):
            k = mp.mpf(s + 1) / N
            P[e, s] = z ** ((s + 1) * e) * (1 - z ** (s + 1)) * (-mp.mpf(1) / N) * mp.beta(k, k)
    Pair = mp.matrix(n, n)
    for a in range(n):
        b = N - 2 - a
        Pair[a, b] = 2j * mp.pi * (-mp.mpf(1) / (N - 2 - 2 * a))
    Pinv = mp.inverse(P)
    Jinv = Pinv.T * Pair * Pinv
    J = mp.inverse(Jinv)
    print(f"N = {N}, genus {g}")
    maxim = max(abs(mp.im(J[i, j])) for i in range(n) for j in range(n))
    print("  max |Im J| =", mp.nstr(maxim, 5))
    Jr = [[mp.re(J[i, j]) for j in range(n)] for i in range(n)]
    dev = max(abs(Jr[i][j] - mp.nint(Jr[i][j])) for i in range(n) for j in range(n))
    print("  max distance of Re J to integers =", mp.nstr(dev, 5))
    Ji = [[int(mp.nint(Jr[i][j])) for j in range(n)] for i in range(n)]
    for row in Ji:
        print("   ", row)
    asym = all(Ji[i][j] == -Ji[j][i] for i in range(n) for j in range(n))
    import sympy
    d = sympy.Matrix(Ji).det()
    print("  antisymmetric:", asym, " det J =", d, " => index [H1 : Z[zeta]gamma] =", sympy.sqrt(abs(d)))
    # E for L = 3 Theta on this lattice: 3J, Pfaffian 3^g * index
    print("  Pf(3J) = 3^g * index =", 3 ** g * sympy.sqrt(abs(d)))


for N in (5, 7):
    run(N)
