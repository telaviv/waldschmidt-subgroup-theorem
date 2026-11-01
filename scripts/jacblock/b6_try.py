from jb_common import *
gens = GENS + [X[0], X[4], X[8]]
tot = 0
for v in (1, 2, 3, 5, 6, 7):
    for e in range(1, 6):
        cof = member(X[v] ** e, gens)
        if cof is not None:
            print('v', v, 'e', e, 'sizes', [nterms(c) for c in cof]); tot += e - 1
            break
print('hilb_deg =', tot + 1)
# with only quadrics (no cubics)
for v in (1, 2, 3, 5, 6, 7):
    for e in range(1, 6):
        if member(X[v] ** e, Q + [X[0], X[4], X[8]]) is not None:
            print('quadrics only: v', v, 'e', e); break
