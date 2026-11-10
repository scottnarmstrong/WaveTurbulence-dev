import sys
sys.path.insert(0, sys.argv[2])
from ylem1_check import *
N = int(sys.argv[1])
vc2 = vine_closures(N, 2); vc1 = vine_closures(N, 1)
fam = inverse_family(N)
from collections import defaultdict
by = defaultdict(lambda: [0, 0, 0])
for c, (g, d) in fam.items():
    by[c[0]][0] += 1
    if c not in vc1: by[c[0]][1] += 1
    if c not in vc2: by[c[0]][2] += 1
print('atoms: #molecules reaching Q/T (<=2 seq) | #not vine closures (m>=1) | (m>=2)')
for n in sorted(by): print(n, by[n])
print('vine closures not reached:', [d for c, d in vc1.items() if c not in fam])
