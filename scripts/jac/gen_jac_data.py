"""Stage A1c data generator (UNTRUSTED: Lean re-checks everything it emits).

Writes, under LSG/Jac/Data/:
  Table.lean   -- the degree-4 normal-form table modulo the 9 quadrics (495 leaves, 144 standard monomials),
                  as a binary search tree `nfTree` keyed by monomial codes, with Kronecker packings kx/ky;
                  the standard-monomial codes `stdc`, the key list `keys`, the row-L1 bound `rowM`, quadrics `Qd`.
  NFCert.lean  -- for every degree-4 monomial mu: cofactors c_j (degree 2) with
                  delta * X^mu - NF(mu) = sum_j c_j Q_j   (delta = 23040, all integers).
  Laws.lean    -- the 81 law coordinates A_k^(m)(X, Y) scaled by 32, as sparse bihomogeneous (2,2) polynomials.

Monomial code: X^e  <->  sum_i e_i 8^i  (9 variables, every exponent < 8).
Sparse polynomial row entry: (code, |coeff|, coeff < 0).

Usage (from lean_lsg/):  python scripts/jac/gen_jac_data.py
"""
import itertools
import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
SPIKE = os.path.join(HERE, '..', 'abvar_spike')
sys.path.insert(0, SPIKE)
OUT = os.path.join(HERE, '..', '..', 'LSG', 'Jac', 'Data')

import flint  # noqa: E402

DELTA = 23040
LAWSCALE = 32
NSTD = 144


def code(m):
    return sum(8 ** i for i in m)


def load():
    cwd = os.getcwd()
    os.chdir(SPIKE)
    try:
        from cert_sizes import Lifter, monos4, monos2
        quads = [{tuple(m): c for m, c in q} for q in json.load(open('ideal.json'))['quadrics']]
        lq = json.load(open('laws_Q.json'))
        L = Lifter(quads)
    finally:
        os.chdir(cwd)
    return quads, lq, L, monos4, monos2


def sgn_entry(c, v):
    v = int(v)
    return f'({c}, {abs(v)}, {"true" if v < 0 else "false"})'


def lean_list(items, per_line=6, indent='  '):
    if not items:
        return '[]'
    lines = []
    for i in range(0, len(items), per_line):
        lines.append(indent + ', '.join(items[i:i + per_line]))
    return '[\n' + ',\n'.join(lines) + ']'


def main():
    quads, lq, L, monos4, monos2 = load()
    # ---------------------------------------------------------------- normal-form table
    rows = {}
    certs = {}
    for c, mono in enumerate(monos4):
        nf, cof = L.lift({c: flint.fmpq(1)})
        rows[mono] = {col: v * DELTA for col, v in nf.items()}
        cj = [dict() for _ in range(9)]
        for (m2, i), v in cof.items():
            w = v * DELTA
            assert w.q == 1
            cj[i][code(m2)] = int(w.p)
        certs[mono] = cj
        for v in rows[mono].values():
            assert v.q == 1
    stdcols = sorted({col for r in rows.values() for col in r})
    assert len(stdcols) == NSTD
    tpos = {col: t for t, col in enumerate(stdcols)}
    stdc = [code(monos4[col]) for col in stdcols]
    keyed = sorted(monos4, key=code)
    keys = [code(m) for m in keyed]
    assert len(set(keys)) == len(keys) == 495
    rowL1 = {m: sum(abs(int(v.p)) for v in rows[m].values()) for m in monos4}
    M = max(rowL1.values())
    # ---------------------------------------------------------------- laws
    std2 = [tuple(s) for s in lq['std']]
    laws = {}
    for key, terms in lq['laws'].items():
        k, m = map(int, key.split(','))
        byal = {}
        for e, cstr in terms:
            al = tuple(i for i in range(9) for _ in range(e[i]))
            be = tuple(i for i in range(9) for _ in range(e[9 + i]))
            v = Fraction(cstr) * LAWSCALE
            assert v.denominator == 1
            byal.setdefault(code(al), []).append((code(be), int(v)))
        laws[(k, m)] = sorted((a, sorted(r)) for a, r in byal.items())

    def n1(law):
        return sum(abs(c) for _, r in law for _, c in r)

    # bound for the identities to be certified: V2' (k, m in 0..8) and V1 (law 0, j)
    wmax = 0
    for k in range(9):
        for m in range(9):
            w = n1(laws[(k, m)]) * n1(laws[(0, 0)]) + n1(laws[(k, 0)]) * n1(laws[(0, m)])
            wmax = max(wmax, w)
    for j in range(9):
        w = sum(abs(c) * n1(laws[(a, 0)]) * n1(laws[(b, 0)]) for (a, b), c in quads[j].items())
        wmax = max(wmax, w)
    bound = wmax * M * M
    # headroom of 2^8 for later identities with larger cofactor weight (G1 / flow identities)
    b = bound.bit_length() + 8
    print(f'M = {M} ({M.bit_length()} bits), max wsum = {wmax}, bound bits = {bound.bit_length()}, b = {b}')
    W = NSTD * b

    # ---------------------------------------------------------------- Table.lean
    def nat_pair(row, width):
        pp, nn = [], []
        for t, v in sorted(row):
            (pp if v > 0 else nn).append(f'({abs(v)} <<< {width * t})')
        return '(' + (' + '.join(pp) if pp else '0') + ', ' + (' + '.join(nn) if nn else '0') + ')'

    leaf_defs = []
    for idx, m in enumerate(keyed):
        row = sorted((tpos[col], int(v.p)) for col, v in rows[m].items())
        rtxt = '[' + ', '.join(sgn_entry(t, v) for t, v in row) + ']'
        leaf_defs.append(f'noncomputable def lf{idx} : Leaf := ⟨{code(m)}, {idx}, {rtxt},\n  {nat_pair(row, b)}⟩')

    def tree(lo, hi):
        if hi - lo == 1:
            return f'(.leaf lf{lo})'
        mid = (lo + hi) // 2
        return f'(.node {keys[mid]} {tree(lo, mid)} {tree(mid, hi)})'

    qd = []
    for q in quads:
        qd.append('[' + ', '.join(sgn_entry(code(mm), c) for mm, c in sorted(q.items(), key=lambda t: code(t[0]))) + ']')
    deg2 = sorted(code(m) for m in monos2)
    out = ['import LSG.Jac.Checker', '', '/-! GENERATED by scripts/jac/gen_jac_data.py — do not edit.',
           '',
           'The degree-4 normal-form table modulo the 9 quadrics of the P⁸ model (ABVAR A0.1), scaled by',
           f'`nfDelta = {DELTA}`; every entry is re-checked in Lean (`LSG.Jac.TableFacts`). -/',
           '',
           'namespace LSG.Jac.Data',
           '',
           'open LSG.Jac',
           '',
           'set_option maxRecDepth 100000',
           '',
           f'/-- Slot width of the inner Kronecker packing (bits). -/\ndef kb : Nat := {b}',
           f'/-- Upper bound for the `L¹` norm of every normal-form row. -/\ndef rowM : Nat := {M}',
           f'/-- The scale of the normal-form rows. -/\ndef nfDelta : Nat := {DELTA}',
           '',
           '/-- The 9 quadrics `Q₀ … Q₈` (codes of degree-2 monomials). -/',
           'def Qd : List (List (Nat × Nat × Bool)) := ' + lean_list(qd, 1),
           '',
           '/-- Codes of the 144 standard monomials of degree 4, in slot order. -/',
           'def stdc : List Nat := ' + lean_list([str(c) for c in stdc], 12),
           '',
           '/-- Codes of all 495 monomials of degree 4, increasing (`keys[i]` is the key of leaf `i`). -/',
           'def keys : List Nat := ' + lean_list([str(c) for c in keys], 12),
           '',
           '/-- Codes of all 45 monomials of degree 2, increasing. -/',
           'def deg2 : List Nat := ' + lean_list([str(c) for c in deg2], 12),
           '']
    out += leaf_defs
    out += ['', '/-- The normal-form table as a search tree on codes. -/',
            'noncomputable def nfTree : T := ' + tree(0, len(keyed)), '', 'end LSG.Jac.Data', '']
    os.makedirs(OUT, exist_ok=True)
    with open(os.path.join(OUT, 'Table.lean'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(out))

    # ---------------------------------------------------------------- NFCert.lean
    out = ['import LSG.Jac.Checker', '', '/-! GENERATED by scripts/jac/gen_jac_data.py — do not edit.',
           '',
           'Normal-form certificates: for each degree-4 monomial `X^μ` (by code), cofactors `c₀ … c₈` of degree 2 with',
           '`nfDelta · X^μ − NF(μ) = Σ_j c_j Q_j`. Checked in `LSG.Jac.TableFacts`. -/',
           '',
           'namespace LSG.Jac.Data',
           '',
           'set_option maxRecDepth 100000',
           '']
    names = []
    for idx, m in enumerate(keyed):
        cj = certs[m]
        parts = []
        for j in range(9):
            parts.append('[' + ', '.join(sgn_entry(c, v) for c, v in sorted(cj[j].items())) + ']')
        out.append(f'noncomputable def nc{idx} : Nat × List (List (Nat × Nat × Bool)) := ({code(m)}, [{", ".join(parts)}])')
        names.append(f'nc{idx}')
    out += ['', '/-- All normal-form certificates, in key order. -/',
            'noncomputable def nfCert : List (Nat × List (List (Nat × Nat × Bool))) := ' + lean_list(names, 16), '',
            'end LSG.Jac.Data', '']
    with open(os.path.join(OUT, 'NFCert.lean'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(out))

    # ---------------------------------------------------------------- Laws.lean
    out = ['import LSG.Jac.Checker', '', '/-! GENERATED by scripts/jac/gen_jac_data.py — do not edit.',
           '',
           f'The 81 coordinates `A_k^(m)(X, Y)` of the 9 addition laws (ABVAR A0.2), scaled by {LAWSCALE}: `law k m` is',
           'a list of rows `(code of X^α, [(code of Y^β, |c|, c < 0)])`. -/',
           '',
           'namespace LSG.Jac.Data',
           '',
           'open LSG.Jac',
           '',
           'set_option maxRecDepth 100000',
           '']
    for k in range(9):
        for m in range(9):
            law = laws[(k, m)]
            rws = []
            for a, r in law:
                rws.append(f'({a}, [' + ', '.join(sgn_entry(bb, c) for bb, c in r) + '])')
            yc = sorted({bb for _, r in law for bb, _ in r})
            out.append(f'/-- `{LAWSCALE} · A_{k}^({m})`. -/')
            out.append(f'noncomputable def L{k}{m} : SP := ⟨{lean_list(rws, 1)},\n  {yc}⟩')
            out.append('')
    out.append('/-- The law coordinates as a table of rows. -/')
    out.append('noncomputable def lawL : List (List SP) := [' + ', '.join(
        '[' + ', '.join(f'L{k}{m}' for m in range(9)) + ']' for k in range(9)) + ']')
    out.append('')
    out.append('/-- The law coordinates: `law k m = 32 · A_k^(m)`. -/')
    out.append('noncomputable def law (k m : Nat) : SP := (lawL.getD k []).getD m ⟨[], []⟩')
    out += ['', 'end LSG.Jac.Data', '']
    with open(os.path.join(OUT, 'Laws.lean'), 'w', encoding='utf-8') as fh:
        fh.write('\n'.join(out))
    json.dump({'b': b, 'M': M, 'delta': DELTA, 'wmax': wmax}, open(os.path.join(HERE, 'table_params.json'), 'w'))
    print('wrote', OUT)


if __name__ == '__main__':
    main()
