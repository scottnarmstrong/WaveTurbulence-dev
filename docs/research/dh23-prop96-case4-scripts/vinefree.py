"""N_m contains no vine-like object (DH23 Def 5.1 L789-L808, Lemma 8.1 L1619): enumerate every atomic group S of N_m
that is a block (DH23 Def 4.10 L712: all atoms of S have degree 4 inside S except exactly two joints with in = out = 1
inside S) or a hyper-block (a block plus one bond between its joints), and test S (resp. S minus the joint bond)
for undirected isomorphism with
  * the eight B2 vine templates (copied verbatim from ylem1-investigation/enum/enum_ylem1.py, which copies
    WaveB2-Molecules.lean), with up to K rungs in each ladder slot;
  * the Q-block = vine (II) with one double bond (the m = 1 case of DH23 Fig. VineAnnotated (A), L1421);
  * two vines (V) sharing both joints (DV) is covered because a DV contains a vine (V) block.
Undirected isomorphism is necessary for being a vine, so 'no match' proves 'no vine-like object'.
Also prints the list of all blocks / hyper-blocks found, and checks the structural facts used in NOTE.md Lemma 3.3:
every block of N_m is a union of consecutive T-blocks, and no vine template (any rungs <= K) has an interior atom whose
removal disconnects the template.
Usage: python3 -I vinefree.py [mmax] [K]
"""
import os, sys, itertools
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from graphs import mk, canon
from necklace import necklace

T = {
 'I': (2, [(0,1),(0,1)], []),
 'II': (6, [(0,2),(0,3),(2,3),(2,3),(4,5),(4,5),(1,4),(1,5),(2,4),(3,5)], [((2,4),(3,5))]),
 'III': (9, [(0,2),(0,3),(2,3),(2,3),(4,5),(4,6),(5,6),(5,6),(7,8),(7,8),(1,7),(1,8),(2,4),(3,5),(4,7),(6,8)],
         [((2,4),(3,5)),((4,7),(6,8))]),
 'IV': (9, [(0,2),(0,3),(2,3),(2,3),(4,5),(4,5),(5,6),(5,6),(7,8),(7,8),(1,7),(1,8),(2,4),(3,6),(4,7),(6,8)],
        [((2,4),(3,6)),((4,7),(6,8))]),
 'V': (9, [(0,1),(0,2),(1,3),(2,3),(2,3),(4,5),(4,5),(4,6),(5,7),(6,7),(6,8),(6,8),(7,8),(7,8),(2,4),(3,5)],
       [((2,4),(3,5))]),
 'VI': (15, [(0,2),(0,3),(2,3),(2,3),(4,5),(4,5),(4,6),(5,8),(6,7),(6,7),(7,9),(8,9),(8,9),(10,11),(10,12),(10,12),
             (11,12),(11,12),(13,14),(13,14),(1,13),(1,14),(2,4),(3,5),(8,10),(9,11),(6,13),(7,14)],
        [((2,4),(3,5)),((8,10),(9,11)),((6,13),(7,14))]),
 'VII': (11, [(0,2),(0,3),(2,3),(2,3),(4,5),(4,5),(4,6),(4,6),(5,6),(7,8),(9,10),(9,10),(1,9),(1,10),(2,7),(3,8),
              (5,7),(6,8),(7,9),(8,10)],
         [((2,7),(3,8)),((5,7),(6,8)),((7,9),(8,10))]),
 'VIII': (11, [(0,2),(0,6),(2,3),(2,3),(4,5),(4,5),(1,4),(1,5),(3,7),(6,7),(6,7),(8,9),(8,10),(8,10),(9,10),(9,10),
               (2,4),(3,5),(6,8),(7,9)],
          [((2,4),(3,5)),((6,8),(7,9))]),
 'II(m=1) Q-block': (4, [(0,2),(0,3),(2,3),(2,3),(1,2),(1,3)], []),
}

def remove_one(lst, e):
    lst = list(lst); lst.remove(e); return lst

def insert_rungs(n, bonds, slot, k):
    if k == 0: return n, bonds
    us = [n+i for i in range(k)]; vs = [n+k+i for i in range(k)]
    b = remove_one(remove_one(bonds, slot[0]), slot[1])
    def rail(z, ws, z2):
        seq = [z] + ws + [z2]; return list(zip(seq[:-1], seq[1:]))
    b += rail(slot[0][0], us, slot[0][1]) + rail(slot[1][0], vs, slot[1][1])
    for u, v in zip(us, vs): b += [(u, v), (u, v)]
    return n + 2*k, b

def expand(X, ks):
    n, b, slots = T[X]
    for s, k in zip(slots, ks):
        n, b = insert_rungs(n, b, s, k)
    return n, b

def vine_canons(K, nmax):
    out = {}
    for X, (n, b, slots) in T.items():
        for ks in itertools.product(range(K + 1), repeat=len(slots)):
            vn, vb = expand(X, ks)
            if vn > nmax: continue
            out.setdefault(canon(mk(vn, vb)), []).append((X, ks))
    return out

def interior_cut_vertex(n, bonds, joints=(0, 1)):
    """Is there an interior atom whose removal disconnects the template?"""
    adj = {v: set() for v in range(n)}
    for a, b in bonds: adj[a].add(b); adj[b].add(a)
    for x in range(n):
        if x in joints: continue
        rest = [v for v in range(n) if v != x]
        seen = {rest[0]}; st = [rest[0]]
        while st:
            y = st.pop()
            for z in adj[y]:
                if z != x and z not in seen: seen.add(z); st.append(z)
        if len(seen) < n - 1: return x
    return None

def blocks(names, bonds):
    n = len(names)
    found = []
    for mask in range(1, 1 << n):
        S = [v for v in range(n) if mask >> v & 1]
        if len(S) < 2: continue
        inn, out = Counter(), Counter()
        inner = []
        for (u, v) in bonds:
            if (mask >> u & 1) and (mask >> v & 1):
                out[u] += 1; inn[v] += 1; inner.append((u, v))
        dS = {v: inn[v] + out[v] for v in S}
        # block: joints with (in,out)=(1,1), all others degree 4 inside S
        j2 = [v for v in S if dS[v] != 4]
        if len(j2) == 2 and all(inn[v] == 1 and out[v] == 1 for v in j2):
            found.append(('block', S, inner, j2))
            continue
        # hyper-block: two joints of degree 3 inside S joined by a bond whose removal gives a block
        if len(j2) == 2 and all(dS[v] == 3 for v in j2):
            a, b = j2
            for k, (u, v) in enumerate(inner):
                if {u, v} == {a, b}:
                    rest = inner[:k] + inner[k+1:]
                    i2, o2 = Counter(), Counter()
                    for (p, q) in rest: o2[p] += 1; i2[q] += 1
                    if all(i2[x] == 1 and o2[x] == 1 for x in (a, b)):
                        found.append(('hyper-block', S, rest, j2)); break
    return found

if __name__ == '__main__':
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    # structural fact: vine templates have no interior cut vertex
    for X in T:
        n, b, slots = T[X]
        for ks in itertools.product(range(3), repeat=len(slots)):
            vn, vb = expand(X, ks)
            assert interior_cut_vertex(vn, vb) is None, (X, ks)
    print(f'vine templates (all eight + Q-block, 0..2 rungs per slot): no interior cut vertex')
    for bead, m in [('T', m) for m in range(1, mmax + 1)] + [('Q', m) for m in range(1, mmax + 1)]:
        names, bonds = necklace(m, bead)
        V = vine_canons(K, len(names))
        fb = blocks(names, bonds)
        hits = []
        for kind, S, inner, js in fb:
            g = mk(len(S), [(S.index(u), S.index(v)) for u, v in inner])
            if canon(g) in V: hits.append((kind, [names[v] for v in S], V[canon(g)]))
        print(f'{bead}-beads m={m}: {len(names)} atoms; {len(fb)} blocks/hyper-blocks; vine matches: {len(hits)}')
        for kind, S, inner, js in fb:
            lbl = sorted(names[v] for v in S)
            ts = sorted({int(x[1:].rstrip("'")) for x in lbl if x[0] in 'efg'})
            consecutive = ts == list(range(ts[0], ts[-1] + 1)) if ts else False
            print(f'   {kind}: joints {[names[v] for v in js]}, T-blocks {ts}, consecutive={consecutive}, atoms={len(S)}')
        for h in hits: print('   VINE MATCH', h)
