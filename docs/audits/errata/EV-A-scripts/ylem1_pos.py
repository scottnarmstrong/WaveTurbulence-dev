import sys
sys.path.insert(0, sys.argv[2])
from ylem1_check import *
N = int(sys.argv[1])
vc1 = vine_closures(N, 1)
# second (Z) inserted into a SINGLE bond created by the first (Z) on T (the "(VI)" bullet, L1946)
res = {}
for e0 in list(T.m):
    for n1 in range(1, N):
        if 3 + 2*n1 > N: break
        h = Z(T, e0, n1)
        newv = sorted(h.vertices() - T.vertices())
        for e in list(h.m):
            if h.m[e] != 1: continue
            if not (set(e) & set(newv)): continue   # bond inserted by first Z
            a, b = e
            # position: 'exit' if one endpoint is an old atom, else ladder rail index
            pos = 'exit' if (set(e) - set(newv)) else 'rail%d' % (min(newv.index(a), newv.index(b)) // 2)
            for n2 in range(1, N):
                if len(h.vertices()) + 2*n2 > N: break
                g = Z(h, e, n2)
                if len(triples(g)) > 2: continue
                c = canon(g)
                res.setdefault((n1, pos, n2), set()).add((c[0], vc1.get(c, 'NOT a vine closure')))
for k in sorted(res):
    print(k, sorted(res[k]))
