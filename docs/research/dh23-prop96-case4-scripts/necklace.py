"""Necklace molecules N_m (NOTE.md, Section 3) and an explicit couple realizing them.

N_m: joints w_0..w_m; T-blocks B_1..B_m, B_i between w_{i-1} (left) and w_i (right), interior e_i, g_i, f_i with
     a->e, b->e, e->g (x2), g->f (x2), f->a, f->b       (a = left joint, b = right joint; parallel double bonds);
     odd block B_0 between w_m (left) and w_0 (right), interior o1, o2 with
     w_m->o1, w_0->o1, o1->o2, o2->w_m, o2->w_0.
Checks (DH23 Def 4.1 L633, Def 4.2, Prop 4.3, Remark 4.4 L682, Prop 4.8 L700):
  * molecule: in/out degree <= 2, no self loop, connected, two degree-3 atoms, rest degree 4, E = 2n-1, no triple bond;
  * an explicit couple Q (two ternary trees, signs (z,-z,z), leaf pairing with opposite signs) with M(Q) = N_m,
    rebuilt from Q by the rules of Def 4.2 and compared bond-by-bond (directed);
  * Q prime (no triple bond in M(Q), DH23 L709) and non-degenerate in the sense of Remark 4.4 (no sibling leaves paired,
    no two siblings whose subtrees' leaves are completely paired among themselves).
Usage: python3 -I necklace.py [m ...]
"""
import sys
from collections import Counter, deque

def necklace(m, kind='T'):
    """kind='T': T-block beads (default); kind='Q': Q-block beads w_{i-1}->s, w_i->s, s->t (x2), t->w_{i-1}, t->w_i."""
    names = []
    idx = {}
    def atom(s):
        idx[s] = len(names); names.append(s); return idx[s]
    W = [atom(f'w{i}') for i in range(m + 1)]
    bonds = []  # directed (u, v) = u -> v
    for i in range(1, m + 1):
        a, b = W[i - 1], W[i]
        if kind == 'T':
            e, g, f = atom(f'e{i}'), atom(f'g{i}'), atom(f'f{i}')
            bonds += [(a, e), (b, e), (e, g), (e, g), (g, f), (g, f), (f, a), (f, b)]
        else:
            e, f = atom(f'e{i}'), atom(f'f{i}')
            bonds += [(a, e), (b, e), (e, f), (e, f), (f, a), (f, b)]
    o1, o2 = atom('o1'), atom('o2')
    a, b = W[m], W[0]
    bonds += [(a, o1), (b, o1), (o1, o2), (o2, a), (o2, b)]
    return names, bonds

def check_molecule(names, bonds):
    n = len(names)
    indeg, outdeg = Counter(), Counter()
    for u, v in bonds:
        assert u != v, 'self loop'
        outdeg[u] += 1; indeg[v] += 1
    deg = [indeg[v] + outdeg[v] for v in range(n)]
    assert all(indeg[v] <= 2 and outdeg[v] <= 2 for v in range(n))
    assert sorted(deg).count(3) == 2 and all(d in (3, 4) for d in deg)
    assert len(bonds) == 2 * n - 1
    und = Counter((min(u, v), max(u, v)) for u, v in bonds)
    assert max(und.values()) <= 2, 'triple bond'
    # connected
    adj = {v: set() for v in range(n)}
    for u, v in bonds: adj[u].add(v); adj[v].add(u)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    assert len(seen) == n
    return deg, indeg, outdeg

def build_couple(names, bonds):
    """Spanning forest (multi-source BFS from the two degree-3 atoms) -> couple. Returns a dict describing Q."""
    n = len(names)
    deg, indeg, outdeg = check_molecule(names, bonds)
    roots = [v for v in range(n) if deg[v] == 3]
    # incident bond ids
    inc = {v: [] for v in range(n)}
    for k, (u, v) in enumerate(bonds):
        inc[u].append(k); inc[v].append(k)
    parent = {r: None for r in roots}; pbond = {r: None for r in roots}
    dq = deque(roots)
    while dq:
        x = dq.popleft()
        for k in inc[x]:
            u, v = bonds[k]; y = v if u == x else u
            if y not in parent:
                parent[y] = x; pbond[y] = k; dq.append(y)
    assert len(parent) == n
    tree_bonds = {pbond[v] for v in range(n) if pbond[v] is not None}
    # signs: root sign + iff (in,out) = (2,1); non-root c: + iff parent bond is c -> parent
    sign = {}
    for v in range(n):
        if parent[v] is None:
            sign[v] = +1 if (indeg[v], outdeg[v]) == (2, 1) else -1
        else:
            u, w = bonds[pbond[v]]
            sign[v] = +1 if u == v else -1
    assert sorted(sign[r] for r in roots) == [-1, 1]
    # children slots
    leaves = []          # leaf id -> (atom, sign, bond id)
    children = {v: [] for v in range(n)}  # list of ('node', c) or ('leaf', leaf_id)
    for v in range(n):
        for k in inc[v]:
            if k == pbond[v]: continue
            u, w = bonds[k]
            if k in tree_bonds:   # v is the parent of the other endpoint
                c = w if u == v else u
                assert parent[c] == v
                children[v].append(('node', c))
            else:
                s = -1 if u == v else +1   # outgoing LP bond <-> child leaf of sign -
                leaves.append((v, s, k)); children[v].append(('leaf', len(leaves) - 1))
    # order children so that signs read (z, -z, z)
    def csign(ch):
        return sign[ch[1]] if ch[0] == 'node' else leaves[ch[1]][1]
    for v in range(n):
        ch = children[v]
        assert len(ch) == 3, (names[v], ch)
        z = sign[v]
        mids = [c for c in ch if csign(c) == -z]; sides = [c for c in ch if csign(c) == z]
        assert len(mids) == 1 and len(sides) == 2, (names[v], [csign(c) for c in ch])
        children[v] = [sides[0], mids[0], sides[1]]
    # leaf pairing: the two leaves created from the same LP bond
    pair = {}
    byb = {}
    for lid, (v, s, k) in enumerate(leaves):
        byb.setdefault(k, []).append(lid)
    for k, ls in byb.items():
        assert len(ls) == 2
        a, b = ls; pair[a] = b; pair[b] = a
        assert leaves[a][1] == -leaves[b][1]
    return dict(roots=roots, parent=parent, sign=sign, children=children, leaves=leaves, pair=pair)

def molecule_from_couple(Q, n):
    """Rebuild M(Q) by DH23 Def 4.2 (L645-L651)."""
    sign, children, leaves, pair = Q['sign'], Q['children'], Q['leaves'], Q['pair']
    out = []
    for v in range(n):
        for ch in children[v]:
            if ch[0] == 'node':
                c = ch[1]
                out.append((v, c) if sign[c] == -1 else (c, v))   # PC bond
    done = set()
    for a, b in pair.items():
        if (b, a) in done: continue
        done.add((a, b))
        va, sa, _ = leaves[a]; vb, sb, _ = leaves[b]
        out.append((va, vb) if sa == -1 else (vb, va))            # LP bond: from '-' leaf atom to '+' leaf atom
    return out

def check_couple(Q, n):
    sign, children, leaves, pair = Q['sign'], Q['children'], Q['leaves'], Q['pair']
    # sign pattern of children
    for v in range(n):
        z = sign[v]
        sg = [sign[c[1]] if c[0] == 'node' else leaves[c[1]][1] for c in children[v]]
        assert sg == [z, -z, z]
    # no sibling leaves paired
    for v in range(n):
        ls = [c[1] for c in children[v] if c[0] == 'leaf']
        for a in ls:
            assert pair[a] not in ls, 'siblings paired'
    # subtree leaves
    memo = {}
    def sub_leaves(ch):
        if ch[0] == 'leaf': return frozenset([ch[1]])
        c = ch[1]
        if c not in memo:
            s = set()
            for cc in children[c]: s |= sub_leaves(cc)
            memo[c] = frozenset(s)
        return memo[c]
    for v in range(n):
        ch = children[v]
        for i in range(3):
            for j in range(i + 1, 3):
                U = sub_leaves(ch[i]) | sub_leaves(ch[j])
                assert not all(pair[l] in U for l in U), 'degenerate siblings (Remark 4.4)'
    # every leaf paired, tree sizes
    assert len(pair) == len(leaves)
    return True

if __name__ == '__main__':
    ms = [int(a) for a in sys.argv[1:]] or [1, 2, 3, 4, 5, 8, 20]
    for kind, m in [('T', m) for m in ms] + [('Q', m) for m in ms]:
        names, bonds = necklace(m, kind)
        n = len(names)
        check_molecule(names, bonds)
        Q = build_couple(names, bonds)
        check_couple(Q, n)
        rebuilt = molecule_from_couple(Q, n)
        assert Counter(rebuilt) == Counter(bonds), 'M(Q) != N_m'
        sizes = Counter()
        for v in range(n):
            r = v
            while Q['parent'][r] is not None: r = Q['parent'][r]
            sizes[names[r]] += 1
        print(f'{kind}-beads m={m}: n={n} atoms, {len(bonds)} bonds (=2n-1), no triple bond; couple built: tree orders {dict(sizes)}, '
              f'{len(Q["leaves"])} leaves, signs/pairing/non-degeneracy OK; M(Q) == N_m (directed): True')
    names, bonds = necklace(3)
    print('\nN_3 bonds (u->v):')
    print('  ' + ', '.join(f'{names[u]}->{names[v]}' for u, v in bonds))
