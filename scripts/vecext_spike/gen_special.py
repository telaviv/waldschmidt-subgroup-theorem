"""Special configurations for (b): identities at P = O-fibre, Q = O-fibre, P = -Q, P = Q (doubling).
Verifies each identity modulo the curve equation hP : y^2 = 4x^3 - g2 x - g3 and writes
LSG/Elliptic/NaturalLawsSpecial.lean.   Usage: python gen_special.py OUTDIR"""
import pickle, re, sys
from common import *

def wrap(s, indent, first=0, width=100):
    toks = re.split(r'( [+-] )', s)
    lines, cur = [], toks[0]
    i = 1
    lim = width - indent
    curlim = width - first
    while i < len(toks):
        op, t = toks[i], toks[i + 1]
        if len(cur) + len(op) + len(t) > curlim:
            lines.append(cur)
            cur = op.strip() + ' ' + t
            curlim = lim
        else:
            cur += op + t
        i += 2
    lines.append(cur)
    return (chr(10) + ' ' * indent).join(lines)

OUT = sys.argv[1]
L5 = pickle.load(open('laws5.pkl', 'rb'))
x, y = sp.symbols('x y')
SUBL = {'x': 'x', 'y': 'y'}

def leanxy(e):
    s = sp.sstr(sp.expand(e), order='lex').replace('**', '^')
    s = re.sub(r'\b(g2|g3)\b', lambda m: {'g2': 'g₂', 'g3': 'g₃'}[m.group(1)], s)
    return s

curve = y**2 - (4*x**3 - g2*x - g3)

def cof(diff):
    diff = sp.expand(diff)
    if diff == 0:
        return 0
    q, r = sp.div(sp.Poly(diff, y), sp.Poly(curve, y))
    r = sp.expand(r.as_expr())
    assert r == 0, ('remainder', r)
    return sp.expand(q.as_expr())

def ev(p, P, Q):
    return sp.expand(p.subs({U1: P[0], V1: P[1], W1: P[2], U2: Q[0], V2: Q[1], W2: Q[2]},
                            simultaneous=True))

sub_ = {1: '₁', 2: '₂'}
order = [(i, l, m) for i in (1, 2) for l in 'VW' for m in 'VW']
O = (0, 1, 0); A = (x, y, 1); An = (x, -y, 1)
# lean renderings of the special argument lists
ARG = {('O', 'A'): 'g₂ g₃ 0 1 0 x y 1', ('A', 'O'): 'g₂ g₃ x y 1 0 1 0',
       ('O', 'O'): 'g₂ g₃ 0 1 0 0 1 0', ('A', 'An'): 'g₂ g₃ x y 1 x (-y) 1',
       ('A', 'A'): 'g₂ g₃ x y 1 x y 1'}
PT = {'O': O, 'A': A, 'An': An}

out = []
out.append('''/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import LSG.Elliptic.NaturalLawsPoly

/-!
# Identities for the special configurations of (b)

Values of the `E`-laws and of the fibre corrections `κ` at the special pairs
`(O, A)`, `(A, O)`, `(O, O)`, `(A, −A)`, `(A, A)` with `A = (x : y : 1)`, `−A = (x : −y : 1)`,
`O = (0 : 1 : 0)`, modulo `y² = 4x³ − g₂x − g₃`. Generated and checked by `gen_special.py` (sympy).
Used in `NaturalGroupFull`.
-/

namespace LSG.Elliptic

variable {R : Type*} [CommRing R] {g₂ g₃ x y : R} (hP : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃)

/-- `4(2y)² x₃` at the doubling point. -/
def dblN3 (g₂ x y : R) : R := (12 * x ^ 2 - g₂) ^ 2 - 8 * x * (2 * y) ^ 2

/-- `8(2y)³ y₃` at the doubling point. -/
def dblY3 (g₂ x y : R) : R :=
  -2 * (12 * x ^ 2 - g₂) * (dblN3 g₂ x y - 4 * (2 * y) ^ 2 * x) - 8 * (2 * y) ^ 3 * y
''')
count = [0]
def emit(name, lhs_l, rhs_l, lhs_s, rhs_s, unf):
    q = cof(lhs_s - rhs_s)
    count[0] += 1
    if q == 0 and name.endswith('_OO'):
        prf = f'  simp only [{unf}]\n  ring'
        head = f'theorem {name} (g₂ g₃ : R) :'
    elif q == 0:
        prf = f'  linear_combination (norm := (simp only [{unf}]; ring)) 0 * hP'
        head = f'include hP in\ntheorem {name} :'
    else:
        prf = (f'  linear_combination (norm := (simp only [{unf}]; ring))\n'
               f'    ({wrap(leanxy(q), 6, 5, 90)}) * hP')
        head = f'include hP in\ntheorem {name} :'
    out.append(f'{head}\n    {lhs_l} =\n      {rhs_l} := by\n{prf}\n')

LAMs = {'V': lambda P: P[1], 'W': lambda P: P[2]}
LAMl = {('V', 'O'): '1', ('W', 'O'): '0', ('V', 'A'): 'y', ('W', 'A'): '1', ('V', 'An'): '(-y)',
        ('W', 'An'): '1'}
RHOs = {'V': lambda P: 2*P[0]**2 if P[2] == 1 else 0, 'W': lambda P: 0}
RHOl = {('V', 'A'): '(2 * x ^ 2)', ('W', 'A'): '0', ('V', 'An'): '(2 * x ^ 2)', ('W', 'An'): '0',
        ('V', 'O'): '0', ('W', 'O'): '0'}

# ---- law values ----
S = {('O', 'A', 1): (1, '1'), ('O', 'A', 2): (4*y, '(4 * y)'),
     ('A', 'O', 1): (-1, '(-1)'), ('A', 'O', 2): (4*y, '(4 * y)'),
     ('O', 'O', 1): (0, '0'), ('O', 'O', 2): (4, '4')}
for (p, q_) in [('O', 'A'), ('A', 'O'), ('O', 'O')]:
    base = A if 'A' in (p, q_) else O
    basel = ('x', 'y', '1') if 'A' in (p, q_) else ('0', '1', '0')
    for i in (1, 2):
        s, sl = S[(p, q_, i)]
        for c, nm in enumerate('UVW'):
            val = ev(LAWS[i][c], PT[p], PT[q_])
            emit(f'lawVal{sub_[i]}{nm}_{p}{q_}', f'law{sub_[i]}{nm} {ARG[(p, q_)]}',
                 f'{sl} * {basel[c]}', val, s*base[c], f'law{sub_[i]}{nm}')
for i in (1, 2):
    for nm, c in (('U', 0), ('W', 2)):
        val = ev(LAWS[i][c], A, An)
        emit(f'lawVal{sub_[i]}{nm}_AAn', f'law{sub_[i]}{nm} {ARG[("A", "An")]}', '0', val, 0,
             f'law{sub_[i]}{nm}')

# ---- kappa values ----
for (i, l, m) in order:
    D = L5[(i, l, m)]
    kW, kV = D['kW2'], D['kV2']
    nmi = f'{sub_[i]}{l}{m}'
    # O-left: P = O, Q = A
    s, sl = S[('O', 'A', i)]
    lam = LAMs[l](O); mu = LAMs[m](A); rho = RHOs[m](A)
    laml = LAMl[(l, 'O')]; mul = LAMl[(m, 'A')]; rhol = RHOl[(m, 'A')]
    emit(f'kapWVal{nmi}_OA', f'kapW{nmi} {ARG[("O", "A")]}', f'{laml} * (-2 * {sl} * {rhol})',
         ev(kW, O, A), lam*(-2*s*rho), f'kapW{nmi}')
    emit(f'kapVVal{nmi}_OA', f'kapV{nmi} {ARG[("O", "A")]}',
         f'{laml} * (4 * {mul} * {sl} * x ^ 2 - 2 * {sl} * y * {rhol})',
         ev(kV, O, A), lam*(4*mu*s*x**2 - 2*s*y*rho), f'kapV{nmi}')
    # O-right: P = A, Q = O
    s, sl = S[('A', 'O', i)]
    lam = LAMs[l](A); mu = LAMs[m](O); rho = RHOs[l](A)
    laml = LAMl[(l, 'A')]; mul = LAMl[(m, 'O')]; rhol = RHOl[(l, 'A')]
    emit(f'kapWVal{nmi}_AO', f'kapW{nmi} {ARG[("A", "O")]}', f'{mul} * (-2 * {sl} * {rhol})',
         ev(kW, A, O), mu*(-2*s*rho), f'kapW{nmi}')
    emit(f'kapVVal{nmi}_AO', f'kapV{nmi} {ARG[("A", "O")]}',
         f'{mul} * (4 * {laml} * {sl} * x ^ 2 - 2 * {sl} * y * {rhol})',
         ev(kV, A, O), mu*(4*lam*s*x**2 - 2*s*y*rho), f'kapV{nmi}')
    # O-O
    emit(f'kapWVal{nmi}_OO', f'kapW{nmi} {ARG[("O", "O")]}', '0', ev(kW, O, O), 0, f'kapW{nmi}')
    emit(f'kapVVal{nmi}_OO', f'kapV{nmi} {ARG[("O", "O")]}', '0', ev(kV, O, O), 0, f'kapV{nmi}')
    # neg: P = A, Q = -A
    lam = LAMs[l](A); mu = LAMs[m](An); rl = RHOs[l](A); rm = RHOs[m](An)
    laml = LAMl[(l, 'A')]; mul = LAMl[(m, 'An')]; rll = RHOl[(l, 'A')]; rml = RHOl[(m, 'An')]
    l1 = ev(LAWS[i][1], A, An)
    emit(f'kapWVal{nmi}_AAn', f'kapW{nmi} {ARG[("A", "An")]}', '0', ev(kW, A, An), 0, f'kapW{nmi}')
    emit(f'kapVVal{nmi}_AAn', f'kapV{nmi} {ARG[("A", "An")]}',
         f'-2 * law{sub_[i]}V {ARG[("A", "An")]} * ({mul} * {rll} + {laml} * {rml})',
         ev(kV, A, An), -2*l1*(mu*rl + lam*rm), f'kapV{nmi}, law{sub_[i]}V')
# ---- doubling ----
Dd = 2*y; e = 12*x**2 - g2
N3d = e**2 - 8*x*Dd**2
Y3d = -2*e*(N3d - 4*Dd**2*x) - 8*Dd**3*y
for i in (1, 2):
    lU, lV, lW = [ev(p, A, A) for p in LAWS[i]]
    s = sub_[i]
    emit(f'dblE1{s}', f'4 * (2 * y) ^ 2 * law{s}U {ARG[("A", "A")]}',
         f'law{s}W {ARG[("A", "A")]} * dblN3 g₂ x y', 4*Dd**2*lU, lW*N3d, f'law{s}U, law{s}W, dblN3')
    emit(f'dblE2{s}', f'8 * (2 * y) ^ 3 * law{s}V {ARG[("A", "A")]}',
         f'law{s}W {ARG[("A", "A")]} * dblY3 g₂ x y', 8*Dd**3*lV, lW*Y3d,
         f'law{s}V, law{s}W, dblY3, dblN3')
for (i, l, m) in order:
    D = L5[(i, l, m)]
    s = sub_[i]; nmi = f'{s}{l}{m}'
    lU, lV, lW = [ev(p, A, A) for p in LAWS[i]]
    kW = ev(D['kW2'], A, A); kV = ev(D['kV2'], A, A)
    lam = LAMs[l](A); mu = LAMs[m](A); rl = RHOs[l](A); rm = RHOs[m](A)
    laml = LAMl[(l, 'A')]; mul = LAMl[(m, 'A')]; rll = RHOl[(l, 'A')]; rml = RHOl[(m, 'A')]
    a = ARG[('A', 'A')]
    emit(f'dblK1{nmi}',
         f'(2 * y) *\n      (kapW{nmi} {a} + 2 * {mul} * law{s}W {a} * {rll} +\n'
         f'        2 * {laml} * law{s}W {a} * {rml})',
         f'{laml} * {mul} * law{s}W {a} * (12 * x ^ 2 - g₂)',
         Dd*(kW + 2*mu*lW*rl + 2*lam*lW*rm), lam*mu*lW*e, f'kapW{nmi}, law{s}W')
    emit(f'dblK3{nmi}',
         f'16 * (2 * y) ^ 4 *\n      (kapV{nmi} {a} + 2 * {mul} * law{s}V {a} * {rll} +\n'
         f'        2 * {laml} * law{s}V {a} * {rml})',
         f'{laml} * {mul} * law{s}W {a} *\n'
         f'        (2 * dblY3 g₂ x y * (12 * x ^ 2 - g₂) + 4 * dblN3 g₂ x y ^ 2)',
         16*Dd**4*(kV + 2*mu*lV*rl + 2*lam*lV*rm), lam*mu*lW*(2*Y3d*e + 4*N3d**2),
         f'kapV{nmi}, law{s}V, law{s}W, dblY3, dblN3')
open(OUT + '/NaturalLawsSpecial.lean', 'w', encoding='utf-8').write(
    '\n'.join(out) + '\nend LSG.Elliptic\n')
print('identities', count[0])
