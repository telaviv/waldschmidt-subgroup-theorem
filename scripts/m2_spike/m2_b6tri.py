"""M2.1 B6, trinomial forms l = X4 + X_b + X_c (UNTRUSTED; see m2_b6lin.py).  Binomials X4 + lam X_b all fail
(m2_b6lin.out: a residual scheme of degree >= 2 remains)."""
import time, itertools
from m2_b6lin import *

def subl(p, coeffs):
    """X4 -> -sum coeffs[b] X_b"""
    rep = -sum((c * x[b] for b, c in coeffs.items()), jb.ZERO)
    return p.compose(*[x[i] if i != 4 else rep for i in range(9)])

t0 = time.time()
good = []
for b, c in itertools.product((6, 7, 8), (0, 1, 2, 3, 5)):
    G8 = [subl(g, {b: 1, c: 1}) for g in GZ]
    h = hf8(G8, 6)
    print(f'l = X4 + X{b} + X{c}: HF_6 = {h}', flush=True)
    if h == 0:
        good.append((b, c))
        if len(good) >= 3:
            break
print('good:', good, f'[{time.time() - t0:.0f}s]', flush=True)
for b, c in good:
    G8 = [subl(g, {b: 1, c: 1}) for g in GZ]
    ev, sz = [], []
    for v in VARS8:
        for e in range(1, 10):
            cof = member8(x[v] ** e, G8)
            if cof is not None:
                ev.append(e); sz.append(sum(nterms(cc) for cc in cof)); break
    hd = 1 + sum(e - 1 for e in ev)
    print(f'l = X4 + X{b} + X{c}: e_v (v = {VARS8}) = {ev}, hilb_deg = {hd}, exact cofactor terms {sz}'
          f' (total {sum(sz)}) [{time.time() - t0:.0f}s]', flush=True)
