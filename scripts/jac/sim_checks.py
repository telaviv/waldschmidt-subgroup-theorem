"""Python mirror of the Lean checks (nfEntryOK, the bidegree checker) on the generated data, to catch generator bugs
before spending kernel time.  Parses LSG/Jac/Data/*.lean.  UNTRUSTED (Lean re-checks)."""
import re, os, json, sys
HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, '..', '..', 'LSG', 'Jac', 'Data')
def trip(s):
    return [(int(a), int(b), c == 'true') for a, b, c in re.findall(r'\((\d+), (\d+), (true|false)\)', s)]
tab = open(os.path.join(D, 'Table.lean'), encoding='utf-8').read()
leaves = {}
for m in re.finditer(r'def lf(\d+) : Leaf := ⟨(\d+), (\d+), \[(.*?)\],', tab):
    leaves[int(m.group(2))] = (int(m.group(3)), trip(m.group(4)))
stdc = [int(x) for x in re.search(r'def stdc : List ℕ := \[(.*?)\]', tab, re.S).group(1).replace('\n', ' ').split(',')]
Qd = [trip(q) for q in re.findall(r'\[((?:\(\d+, \d+, (?:true|false)\)(?:, )?)+)\]', re.search(r'def Qd .*?:= \[(.*?)\]\n\n', tab, re.S).group(1))]
assert len(Qd) == 9, len(Qd)
sv = lambda n, s: -n if s else n
nc = open(os.path.join(D, 'NFCert.lean'), encoding='utf-8').read()
maxw = 0
for m in re.finditer(r'def nc\d+ : .*?:= \((\d+), \[(.*)\]\)', nc):
    mu = int(m.group(1))
    cofs = [trip(c) for c in re.findall(r'\[(.*?)\]', m.group(2))]
    assert len(cofs) == 9
    idx, row = leaves[mu]
    acc = {}
    W = 23040
    acc[mu] = acc.get(mu, 0) + W
    tot = W
    for s, n, ng in row:
        acc[stdc[s]] = acc.get(stdc[s], 0) - sv(n, ng); tot += n
    for c, q in zip(cofs, Qd):
        for a in c:
            for b in q:
                k = a[0] + b[0]
                acc[k] = acc.get(k, 0) - sv(a[1], a[2]) * sv(b[1], b[2]); tot += a[1] * b[1]
                assert k in leaves
    assert all(v == 0 for v in acc.values()), (mu, {k: v for k, v in acc.items() if v})
    maxw = max(maxw, tot)
print('NF certificates OK; max sum|w| =', maxw, maxw.bit_length(), 'bits')
