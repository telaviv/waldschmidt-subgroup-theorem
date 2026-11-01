from jb_common import *
def words_dir(F, v):
    w = [X[0]]
    for k in range(3):
        w.append(Dv(F, v, w[-1]))
    return w
for name, F, c, N in (('W4', W4, 4, 4), ('W8', W8, 8, 5)):
    for dirs in ([(1, 0), (0, 1)], [(1, 0), (0, 1), (1, 1)], [(1, 0), (0, 1), (1, 1), (1, -1)], [(1,0),(0,1),(1,1),(1,-1),(1,2)]):
        gens = GENS + [X[0]]
        labels = [('G', i) for i in range(12)] + [('X0',)]
        for v in dirs:
            ws = words_dir(F, v)
            for k in (1, 2, 3):
                if ws[k] != 0:
                    gens.append(ws[k]); labels.append(('w', v, k))
        weighted = len(dirs) == 2
        cof = member(X[c] ** N, gens, weighted=weighted)
        print(name, dirs, 'found' if cof else 'no')
        if cof:
            print('  used', [(l, nterms(cc)) for l, cc in zip(labels, cof) if cc != 0])
            break
