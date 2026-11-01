import sys
from b5_pick import *
E = int(sys.argv[1])
allF = sorted(SS)
cur = []
def covered(Fs):
    gens = GENS + [SS[F] for F in Fs]
    return [v for v in range(9) if in_ideal_modp(X[v] ** E, gens)]
best = []
while len(best) < 9:
    scores = []
    for F in allF:
        if F in cur: continue
        c = covered(cur + [F])
        scores.append((len(c), -nterms(SS[F]), F))
    scores.sort(reverse=True)
    cur.append(scores[0][2]); best = covered(cur)
    print(len(cur), scores[0], best, flush=True)
    if len(cur) > 12: break
