from jb_common import *
# cubic memberships
for j, C in enumerate(CUB):
    for k in range(9):
        cof = member(X[k] * C, Q)
        assert cof is not None
    print('cubic', j, 'ok; last cof sizes', [nterms(c) for c in cof])
# tangency
for name, F in (('W4', W4), ('W8', W8)):
    for j in range(2):
        for i, G in enumerate(GENS):
            T = D(F, j, G)
            cof = member(T, GENS)
            assert cof is not None, (name, j, i)
        print(name, j, 'tangency ok')
# words
for name, F, c, N in (('W4', W4, 4, 4), ('W8', W8, 8, 5)):
    words = {(): X[0]}
    for k in range(1, 4):
        for w in itertools.product((0, 1), repeat=k):
            words[w] = D(F, w[0], words[w[1:]])
    sym = {}
    for k in range(1, 4):
        for n0 in range(k + 1):
            sym[(k, n0)] = sum((words[w] for w in itertools.product((0, 1), repeat=k) if w.count(0) == n0), ZERO)
    print(name, {kk: nterms(v) for kk, v in sym.items()})
    gens = GENS + [X[0]] + [sym[kk] for kk in sorted(sym)]
    T = X[c] ** N
    cof = member(T, gens)
    print(name, 'exit N =', N, 'found' if cof else 'NOT found')
    if cof:
        print('  cof sizes', [nterms(x) for x in cof])
