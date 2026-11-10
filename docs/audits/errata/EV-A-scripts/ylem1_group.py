import sys
sys.path.insert(0, sys.argv[2])
from ylem1_check import *
N = int(sys.argv[1])
vc1 = vine_closures(N, 1)
groups = {}
for e0 in list(T.m):
    for n1 in range(1, N):
        if 3 + 2*n1 > N: break
        h = Z(T, e0, n1)
        newv = sorted(h.vertices() - T.vertices())
        for e in list(h.m):
            if h.m[e] == 3: continue
            a, b = e
            if set(e) <= set(T.vertices()):
                bullet = 'IV(other bond of same double)' if norm(e) == norm(e0) else 'III(another double of T)'
            elif h.m[e] == 2:
                bullet = 'VII(inserted double)'
            else:
                pos = 'exit' if (set(e) - set(newv)) else 'rail%d' % (min(newv.index(a), newv.index(b)) // 2)
                bullet = 'VI(inserted single,%s)' % pos
            for n2 in range(1, N):
                if len(h.vertices()) + 2*n2 > N: break
                g = Z(h, e, n2)
                if len(triples(g)) > 2: continue
                c = canon(g)
                if c in vc1: continue
                groups.setdefault(c, set()).add((n1, bullet, n2))
for c in sorted(groups, key=lambda c: c[0]):
    print(c[0], sorted(groups[c]))
