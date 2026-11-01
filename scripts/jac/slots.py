"""Python mirror of the checker accumulator (`evalO`/`evalFrom`), parsing the generated Lean data, used to produce the
literal intermediate slot lists of split certificates. UNTRUSTED (the kernel re-checks `slotsEq`)."""
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, '..', '..', 'LSG', 'Jac', 'Data')


def trip(s):
    return [(int(a), int(b), c == 'true') for a, b, c in re.findall(r'\((\d+), (\d+), (true|false)\)', s)]


def load_table():
    tab = open(os.path.join(D, 'Table.lean'), encoding='utf-8').read()
    kb = int(re.search(r'def kb : Nat := (\d+)', tab).group(1))
    rows = {}
    for m in re.finditer(r'def lf\d+ : Leaf := ⟨(\d+), (\d+), \[(.*?)\],', tab):
        rows[int(m.group(1))] = trip(m.group(3))
    return kb, rows


def load_laws():
    s = open(os.path.join(D, 'Laws.lean'), encoding='utf-8').read()
    laws = {}
    for m in re.finditer(r'def L(\d)(\d) : SP := ⟨\[(.*?)\],\n', s, re.S):
        rows = []
        for rm in re.finditer(r'\((\d+), \[(.*?)\]\)', m.group(3)):
            rows.append((int(rm.group(1)), trip(rm.group(2))))
        laws[(int(m.group(1)), int(m.group(2)))] = rows
    return laws


def sv(n, s):
    return -n if s else n


def eval_slots(terms, kb, rows, start=None):
    """terms: list of (c, neg, A_rows, B_rows). Returns dict slot -> signed int."""
    ky = {}

    def KY(nu):
        if nu not in ky:
            ky[nu] = sum(sv(v, sg) << (kb * t) for t, v, sg in rows[nu])
        return ky[nu]
    acc = dict(start or {})
    for c, neg, A, B in terms:
        for a, ra in A:
            for b, rb in B:
                inner = 0
                for bt, ct, st in ra:
                    for bu, cu, su in rb:
                        inner += sv(ct, st) * sv(cu, su) * KY(bt + bu)
                for s, v, sg in rows[a + b]:
                    acc[s] = acc.get(s, 0) + sv(c, neg) * sv(v, sg) * inner
    return acc


def lean_slot_list(acc):
    n = max(acc) + 1 if acc else 0
    items = []
    for s in range(n):
        v = acc.get(s, 0)
        items.append(f'({max(v, 0)}, {max(-v, 0)})')
    return '[' + ', '.join(items) + ']'
