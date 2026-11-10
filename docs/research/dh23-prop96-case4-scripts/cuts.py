"""Stage-2 reduction (DH23 Sec 9.3, Steps 1-4, L1773-L1782; TARGET Operations 1-4, L2140-L2148) on N_m, with the
decoration class of NOTE.md Section 3: the joints w_0..w_m are SG (designated pair = the two bonds of w_i inside one
adjacent bead), every other atom is LG.  Step 1: no SG vine-like object (vinefree.py).  Step 2: a triangle needs two
SG atoms, but no two joints are adjacent.  Step 3: cut the joints, in EVERY order.  Step 4: exhaust beta-cuts.
For each order, list the final components with (V_alpha, V_beta) and flag the T-block components with
V_alpha = 0, V_beta = 2 (DH23 Prop 9.6 proof, case (4), L1883).
Usage: python3 -I cuts.py [m]
"""
import os, sys, itertools
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from necklace import necklace

def components(natoms, bonds, alive):
    adj = {v: set() for v in alive}
    for (u, v) in bonds:
        adj[u].add(v); adj[v].add(u)
    comp = {}; cs = []
    for s in alive:
        if s in comp: continue
        c = [s]; comp[s] = len(cs); st = [s]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in comp: comp[y] = len(cs); c.append(y); st.append(y)
        cs.append(c)
    return comp, cs

def cut(state, v, pair):
    """Cut atom v along bond ids in `pair`: v keeps the other bonds, a new atom v' gets `pair`."""
    names, bonds, kind = state
    new = len(names)
    names = names + [names[v] + "'"]
    bonds = list(bonds)
    for k in pair:
        a, b = bonds[k]
        bonds[k] = (new if a == v else a, new if b == v else b)
    return names, bonds, kind

def degree(bonds, v):
    return sum((a == v) + (b == v) for a, b in bonds)

def run(m, order, bead='T'):
    names, bonds = necklace(m, bead)
    W = [names.index(f'w{i}') for i in range(m + 1)]
    kind = {}
    state = (names, bonds, kind)
    for i in order:
        w = W[i]
        names, bonds, _ = state
        # designated pair: the two bonds of w inside bead B_{i+1} (B_0 for i = m)
        bidx = (i + 1) if i < m else 0
        inbead = []
        for k, (a, b) in enumerate(bonds):
            if w in (a, b):
                o = b if a == w else a
                on = names[o]
                ob = 0 if on in ('o1', 'o2') else int(on[1:]) if on[0] in 'efg' else None
                if ob == bidx: inbead.append(k)
        assert len(inbead) == 2
        before = len(components(len(names), bonds, range(len(names)))[1])
        state = cut(state, w, inbead)
        names, bonds, _ = state
        after = len(components(len(names), bonds, range(len(names)))[1])
        t = 'alpha' if after == before else 'beta'
        kind[w] = t; kind[len(names) - 1] = t
    # Step 2 check: no triangle with two SG atoms (joints are pairwise non-adjacent in N_m)
    # Step 4: look for beta-cuts at atoms of degree 3 or 4
    names, bonds, _ = state
    step4 = []
    for v in range(len(names)):
        if degree(bonds, v) < 3: continue
        inc = [k for k, (a, b) in enumerate(bonds) if v in (a, b)]
        outs = [k for k in inc if bonds[k][0] == v]; ins = [k for k in inc if bonds[k][1] == v]
        base = len(components(len(names), bonds, range(len(names)))[1])
        for k1 in outs:
            for k2 in ins:
                st2 = cut(state, v, [k1, k2])
                if len(components(len(st2[0]), st2[1], range(len(st2[0])))[1]) > base:
                    step4.append((names[v], k1, k2))
    comp, cs = components(len(names), bonds, range(len(names)))
    res = []
    for c in cs:
        na = sorted(names[v] for v in c)
        va = sum(kind.get(v) == 'alpha' for v in c); vb = sum(kind.get(v) == 'beta' for v in c)
        eps = [names[v] for v in c if v not in kind]
        nb = 3 if bead == 'T' else 2
        tblock = len(c) == nb + 2 and sum(x[0] in 'efg' for x in eps) == nb
        odd = any(x in ('o1', 'o2') for x in eps)
        res.append((na, va, vb, tblock, odd))
    return res, step4

if __name__ == '__main__':
    m = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    bead = sys.argv[2] if len(sys.argv) > 2 else 'T'
    allorders = list(itertools.permutations(range(m + 1)))
    every = True
    for order in allorders:
        res, step4 = run(m, order, bead)
        assert not step4, step4
        bad = [r for r in res if r[3] and r[1] == 0 and r[2] == 2]
        every &= bool(bad)
        if order == allorders[0] or order == tuple(range(m + 1)):
            print(f'order {order}:')
            for na, va, vb, tb, odd in res:
                tag = (bead + '-block') if tb else ('odd' if odd else '')
                print(f'   {tag:7s} V_alpha={va} V_beta={vb}  {na}')
    print(f'{bead}-beads m={m}: {len(allorders)} Step-3 orders; Step 4 performs no cut in any order; '
          f'a {bead}-block component with V_alpha=0, V_beta=2 occurs in EVERY order: {every}')
