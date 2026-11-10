import sys
sys.path.insert(0, sys.argv[2])
from ylem1_check import *
N = int(sys.argv[1])
vc2 = vine_closures(N, 2); vc1 = vine_closures(N, 1)
fam = inverse_family(N)
# erratum's T1
T1 = G(5, [(1,0),(1,2),(2,1),(2,0),(0,2),(0,3),(3,4),(3,4),(4,3),(4,1)])
print('erratum T1 canon in family:', canon(T1) in fam, ' in vine closures:', canon(T1) in vc1,
      ' reductions -> T?', all_reductions(T1) == {cT})
for c, (g, d) in sorted(fam.items(), key=lambda x: x[0][0]):
    if c in vc1: continue
    red = all_reductions(g)
    tag = 'T' if red == {cT} else ('Q' if red == {cQ} else str(len(red)) + ' results incl T' if cT in red else 'other')
    trip = triples(g)
    # describe: multiplicities
    vs = sorted(g.vertices()); ren = {v: i for i, v in enumerate(vs)}
    edges = sorted((ren[a], ren[b], c_) for (a, b), c_ in g.m.items())
    # are the two triples adjacent (joined by a single bond)?
    adj = None
    if len(trip) == 2:
        (a, b), (c_, d_) = trip
        adj = any(g.m[norm((x, y))] for x in (a, b) for y in (c_, d_))
    print(f'{c[0]} atoms  {d:22s} triples={len(trip)} triples_adjacent={adj} all-order reductions={tag}')
    print('     ', edges)
