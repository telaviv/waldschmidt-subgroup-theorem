"""Independent checks for the 5-variable model laws (integer-scaled: kappa' = 2 kappa).
(a)  Phi' = lV kW' - lW kV' + 4 M lU^2  in (F_P, F_Q)  (then G(A) = 2 M Phi'), cofactors by division;
(b)  generic: 2(x1-x2) [A_T1 - A_W t3] == 0 and 2(x1-x2)lW... mod curves, at T1 = W t, T3 = V t - 2U^2/W.
"""
import pickle
from common import *

res = pickle.load(open('kappa.pkl', 'rb'))
HV = {'V': (V1, V2), 'W': (W1, W2)}
TL = {'V': (T31, T32), 'W': (T11, T12)}
GENS = [U1, V1, W1, U2, V2, W2]
out = {}
for (i, lam, mu), (kW, kV) in res.items():
    lU, lV, lW = LAWS[i]
    kW2 = sp.expand(2*kW); kV2 = sp.expand(2*kV)
    den = sp.ilcm(*[sp.Rational(c).q for c in sp.Poly(kW2, *GENS, g2, g3).coeffs()] +
                  [sp.Rational(c).q for c in sp.Poly(kV2, *GENS, g2, g3).coeffs()])
    l1 = HV[lam][0]; m2 = HV[mu][1]
    M = l1*m2
    A = [2*M*lU, 2*M*lV, 2*M*lW,
         2*m2*lW*TL[lam][0] + 2*l1*lW*TL[mu][1] - kW2,
         2*m2*lV*TL[lam][0] + 2*l1*lV*TL[mu][1] - kV2]
    A = [sp.expand(a) for a in A]
    # (a) G(A) = A_W A_T3 - A_V A_T1 + 2 A_U^2
    GA = sp.expand(A[2]*A[4] - A[1]*A[3] + 2*A[0]**2)
    Phi = sp.expand(lV*kW2 - lW*kV2 + 4*M*lU**2)
    assert sp.expand(GA - 2*M*Phi) == 0
    FP = F(U1, V1, W1); FQ = F(U2, V2, W2)
    (q1, q2), r = sp.reduced(Phi, [FP, FQ], U1, V1, W1, U2, V2, W2, order='lex')
    assert r == 0, ('remainder', i, lam, mu)
    assert sp.expand(q1*FP + q2*FQ - Phi) == 0
    qden = sp.ilcm(*[sp.Rational(c).q for c in sp.Poly(q1, *GENS, g2, g3).coeffs()] +
                   [sp.Rational(c).q for c in sp.Poly(q2, *GENS, g2, g3).coeffs()])
    # (b) generic, affine points with T1 = t, T3 = y t - 2x^2
    sub = {U1: x1, V1: y1, W1: 1, U2: x2, V2: y2, W2: 1,
           T11: t1, T31: y1*t1 - 2*x1**2, T12: t2, T32: y2*t2 - 2*x2**2}
    Aa = [sp.expand(a.subs(sub)) for a in A]
    # t3 = t1 + t2 - (y1-y2)/(2(x1-x2));  check D*A_T1 = A_W (D (t1+t2) - (y1-y2)), D = 2(x1-x2)
    D = 2*(x1 - x2)
    e1 = nf(D*Aa[3] - Aa[2]*(D*(t1 + t2) - (y1 - y2)))
    # x3 = (y1-y2)^2/(4(x1-x2)^2) - x1 - x2,  y3 = -m (x3 - x1) - y1, m = (y1-y2)/(x1-x2)
    # A_T3 = A_W (y3 t3 - 2 x3^2): multiply by 16 (x1-x2)^4 * D ... check A_W-scaled
    m = (y1 - y2)/(x1 - x2)
    x3 = m**2/4 - x1 - x2
    y3 = -m*(x3 - x1) - y1
    t3 = t1 + t2 - m/2
    e3 = sp.together(Aa[4] - Aa[2]*(y3*t3 - 2*x3**2))
    e3n = nf(sp.numer(e3))
    eU = nf(sp.numer(sp.together(Aa[0] - Aa[2]*x3)))
    eV = nf(sp.numer(sp.together(Aa[1] - Aa[2]*y3)))
    print(i, lam, mu, 'kappa denom', den, 'cofactor denom', qden,
          'terms Phi', len(Phi.args), 'q1', len(q1.args), 'q2', len(q2.args),
          '(b) checks', e1 == 0, e3n == 0, eU == 0, eV == 0, flush=True)
    out[(i, lam, mu)] = dict(kW2=kW2, kV2=kV2, Phi=Phi, q1=q1, q2=q2, A=A)
pickle.dump(out, open('laws5.pkl', 'wb'))
