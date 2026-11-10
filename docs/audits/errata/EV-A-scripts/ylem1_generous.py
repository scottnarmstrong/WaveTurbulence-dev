# "Most generous" reading: a dashed pair joining two double bonds may have length -1,
# i.e. the two rungs are merged into one rung carrying both outer bonds.
import sys, itertools
sys.path.insert(0, sys.argv[2])
from ylem1_check import *
N = int(sys.argv[1])
def build2(spec, dashed, ks):
    E = []
    for (u, v, c) in spec: E += [(u, v)] * c
    ren = {}
    extra = 0
    for ((x, y), (x2, y2)), k in zip(dashed, ks):
        if k >= 0:
            prev, prev2 = x, x2
            for i in range(k):
                r, r2 = f'L{extra}a', f'L{extra}b'; extra += 1
                E += [(prev, r), (prev2, r2), (r, r2), (r, r2)]
                prev, prev2 = r, r2
            E += [(prev, y), (prev2, y2)]
        else:
            dx = sum(1 for e in E if set(e) == {x, x2}); dy = sum(1 for e in E if set(e) == {y, y2})
            if dx != 2 or dy != 2: return None
            E = [e for e in E if set(e) != {y, y2}]   # drop rung y=y2
            ren[y] = x; ren[y2] = x2
    def r(u):
        while u in ren: u = ren[u]
        return u
    E = [(r(a), r(b)) for a, b in E]
    names = sorted({u for e in E for u in e}); ix = {u: i for i, u in enumerate(names)}
    return names, ix, [(ix[a], ix[b]) for a, b in E]
vc = dict(vine_closures(N, 1))
for name, (spec, dashed) in VINES.items() if False else [(k, v) for k, v in VINES.items() if v]:
    for ks in itertools.product(range(-1, N // 2 + 1), repeat=len(dashed)):
        if -1 not in ks: continue
        out = build2(spec, dashed, ks)
        if out is None: continue
        names, ix, E = out
        if len(names) - 2 > N: continue
        try:
            g = closure(names, ix, E)
        except AssertionError:
            continue
        vc.setdefault(canon(g), f'{name}{ks}')
fam = inverse_family(N)
for c, (g, d) in sorted(fam.items(), key=lambda x: x[0][0]):
    print(c[0], d, '->', vc.get(c, 'NOT a closure even generously'))
