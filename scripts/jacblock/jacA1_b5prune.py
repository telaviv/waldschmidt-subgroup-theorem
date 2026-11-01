import sys, itertools
from b5_pick import *
base=[(1,2,3,4,6,7),(1,2,3,4,5,7),(0,1,2,5,6,7),(2,3,4,6,7,8),(1,4,5,6,7,8),(1,2,3,5,6,8)]
for drop in range(1,3):
    for rm in itertools.combinations(range(6), drop):
        Fs=[base[i] for i in range(6) if i not in rm]
        print(rm, cover_degrees(Fs, 8), flush=True)
