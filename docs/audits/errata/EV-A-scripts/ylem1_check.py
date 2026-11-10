# Independent check of DH23 Lemma ylem1 (L1937).
# Undirected loopless multigraphs; a 4-regular loopless multigraph always has an
# Eulerian orientation with in=out=2, and the (Y) operations commute with orientation,
# so undirected analysis suffices both for (Y)-reachability and for non-isomorphism
# with vine closures.
import itertools, sys
from collections import Counter

def norm(e):
    a, b = e
    return (a, b) if a <= b else (b, a)

class G:
    def __init__(self, n, edges):
        self.n = n
        self.m = Counter(norm(e) for e in edges)
        for (a, b) in self.m:
            assert a != b
    def deg(self, v):
        return sum(c for (a, b), c in self.m.items() if v in (a, b))
    def nbrs(self, v):
        out = []
        for (a, b), c in self.m.items():
            if a == v: out += [b] * c
            elif b == v: out += [a] * c
        return out
    def copy(self):
        g = G.__new__(G); g.n = self.n; g.m = Counter(self.m); return g
    def remove_vertex(self, v):
        self.m = Counter({e: c for e, c in self.m.items() if v not in e})
    def vertices(self):
        vs = set()
        for (a, b) in self.m: vs.add(a); vs.add(b)
        return vs

def canon(g):
    """Canonical form of a multigraph (non-isolated vertices only): brute-force
    individualisation-refinement; fine for <= ~15 vertices."""
    vs = sorted(g.vertices())
    idx = {v: i for i, v in enumerate(vs)}
    n = len(vs)
    A = [[0] * n for _ in range(n)]
    for (a, b), c in g.m.items():
        A[idx[a]][idx[b]] = c; A[idx[b]][idx[a]] = c
    def refine(col):
        while True:
            sig = [(col[i], tuple(sorted((col[j], A[i][j]) for j in range(n) if A[i][j]))) for i in range(n)]
            keys = sorted(set(sig))
            new = [keys.index(s) for s in sig]
            if len(set(new)) == len(set(col)):
                return new
            col = new
    best = [None]
    def search(col):
        col = refine(col)
        if len(set(col)) == n:
            perm = sorted(range(n), key=lambda i: col[i])
            M = tuple(tuple(A[perm[i]][perm[j]] for j in range(n)) for i in range(n))
            if best[0] is None or M < best[0]:
                best[0] = M
            return
        cnt = Counter(col)
        target = min((c for c in cnt if cnt[c] > 1), key=lambda c: (cnt[c], c))
        for i in range(n):
            if col[i] == target:
                new = [2 * c + (0 if c < target else 1) if c != target else 2 * c for c in col]
                # individualise i: give it a fresh colour just below the class
                new = [2 * c for c in col]
                new[i] = 2 * target - 1
                search(new)
    search([0] * n)
    return (n, best[0])

# ---------- (Y) operations -------------------------------------------------
def triples(g):
    return [e for e, c in g.m.items() if c == 3]

def y_sequence(g, e):
    """Apply one (Y) sequence starting at triple bond e. Returns new graph and ops list."""
    g = g.copy()
    ops = []
    while True:
        v1, v2 = e
        ext1 = [x for x in g.nbrs(v1) if x != v2]
        ext2 = [x for x in g.nbrs(v2) if x != v1]
        g.remove_vertex(v1); g.remove_vertex(v2)
        if len(ext1) + len(ext2) <= 1 or (len(ext1) == 1 and len(ext2) == 1 and ext1[0] == ext2[0]):
            ops.append('Y1'); return g, ops
        if len(ext1) == 1 and len(ext2) == 1:
            a, b = ext1[0], ext2[0]
            g.m[norm((a, b))] += 1
            ops.append('Y2')
            if g.m[norm((a, b))] == 3:
                e = norm((a, b)); continue
            return g, ops
        # other shapes (degrees not 4) - should not occur for 4-regular input
        ops.append('Y?'); return g, ops

def all_reductions(g, depth=0):
    """All results of applying (Y) sequences until no triple bond, all orders."""
    ts = triples(g)
    if not ts:
        return {canon(g)}
    res = set()
    for e in ts:
        h, _ = y_sequence(g, e)
        res |= all_reductions(h, depth + 1)
    return res

Q = G(2, [(0, 1)] * 4)
T = G(3, [(0, 1), (0, 1), (1, 2), (1, 2), (0, 2), (0, 2)])
cQ, cT = canon(Q), canon(T)

# ---------- inverse (Z): insert a (Y2)-sequence structure with n rungs ---------
def Z(g, e, n):
    p, q = e
    if g.m[e] == 3 or g.m[e] == 0:  # forward would create/continue a triple
        return None
    h = g.copy()
    h.m[e] -= 1
    if h.m[e] == 0: del h.m[e]
    base = max(h.vertices() | {p, q}) + 1
    a = [base + 2 * i for i in range(n)]
    b = [base + 2 * i + 1 for i in range(n)]
    h.m[norm((a[0], b[0]))] += 3
    for i in range(1, n):
        h.m[norm((a[i], b[i]))] += 2
        h.m[norm((a[i - 1], a[i]))] += 1
        h.m[norm((b[i - 1], b[i]))] += 1
    h.m[norm((a[-1], p))] += 1
    h.m[norm((b[-1], q))] += 1
    h.n = base + 2 * n
    return h

def inverse_family(maxatoms):
    out = {}  # canon -> (graph, description)
    level0 = [(Q, 'Q'), (T, 'T')]
    for g, d in level0:
        out.setdefault(canon(g), (g, d + ' (0 seq)'))
    level1 = []
    for g, d in level0:
        for e in list(g.m):
            n = 1
            while len(g.vertices()) + 2 * n <= maxatoms:
                h = Z(g, e, n)
                if h is not None and len(triples(h)) <= 2:
                    level1.append((h, f'{d}+Z{n}'))
                    out.setdefault(canon(h), (h, f'{d}+Z{n} (1 seq)'))
                n += 1
    for g, d in level1:
        for e in list(g.m):
            n = 1
            while len(g.vertices()) + 2 * n <= maxatoms:
                h = Z(g, e, n)
                if h is not None and len(triples(h)) <= 2:
                    out.setdefault(canon(h), (h, f'{d}+Z{n} (2 seq)'))
                n += 1
    return out

# ---------- vines, from DH23 Figure fig:vines and Remark remilia -------------
def build(edges_spec, dashed, ladders):
    """edges_spec: list of (u,v,mult) over named atoms; dashed: list of pairs of
    parallel single bonds ((x,y),(x2,y2)) into which a ladder with k rungs is inserted."""
    edges = []
    for (u, v, c) in edges_spec:
        edges += [(u, v)] * c
    extra = 0
    for ((x, y), (x2, y2)), k in zip(dashed, ladders):
        prev, prev2 = x, x2
        for i in range(k):
            r, r2 = f'L{extra}a', f'L{extra}b'; extra += 1
            edges += [(prev, r), (prev2, r2), (r, r2), (r, r2)]
            prev, prev2 = r, r2
        edges += [(prev, y), (prev2, y2)]
    names = sorted({u for e in edges for u in e})
    ix = {u: i for i, u in enumerate(names)}
    return names, ix, [(ix[a], ix[b]) for a, b in edges]

VINES = {
 'II': None,  # handled separately (ladder of m rungs between joints)
 'III': ([('J1','a1',1),('J1','a2',1),('a1','a2',2),('m1','m2',1),('m1','m3',1),('m2','m3',2),
          ('c1','c2',2),('J2','c1',1),('J2','c2',1)],
         [(('a1','m1'),('a2','m2')), (('m1','c1'),('m3','c2'))]),
 'IV': ([('J1','t1',1),('J1','t2',1),('t1','t2',2),('mL','mC',2),('mC','mR',2),('b1','b2',2),
         ('J2','b1',1),('J2','b2',1)],
        [(('t1','mL'),('t2','mR')), (('mL','b1'),('mR','b2'))]),
 'V': ([('J1','J2',1),('J1','p1',1),('J2','p2',1),('p1','p2',2),('q1','q2',2),('q1','r1',1),
        ('q2','r2',1),('r1','r2',1),('r1','s',2),('r2','s',2)],
       [(('p1','q1'),('p2','q2'))]),
 'VI': ([('J1','A1',1),('J1','A2',1),('A1','A2',2),('B1','B2',2),('B2','D1',1),('B1','C1',1),
         ('C1','C2',2),('C2','D2',1),('D1','D2',2),('E1','F',2),('E2','F',2),('E1','E2',1),
         ('G1','G2',2),('J2','G1',1),('J2','G2',1)],
        [(('A1','B1'),('A2','B2')), (('D1','E1'),('D2','E2')), (('C1','G1'),('C2','G2'))]),
 'VII': ([('J1','P1',1),('J1','P2',1),('P1','P2',2),('T1','T2',2),('T2','T3',2),('T1','T3',1),
          ('M1','M2',1),('Q1','Q2',2),('J2','Q1',1),('J2','Q2',1)],
         [(('P1','M1'),('P2','M2')), (('T1','M1'),('T3','M2')), (('M1','Q1'),('M2','Q2'))]),
 'VIII': ([('J1','U1',1),('J1','B1',1),('U1','U2',2),('R1','R2',2),('J2','R1',1),('J2','R2',1),
           ('U2','B2',1),('B1','B2',2),('S1','S2',1),('S1','S3',2),('S2','S3',2)],
          [(('U1','R1'),('U2','R2')), (('B1','S1'),('B2','S2'))]),
}

def closure(names, ix, edges):
    g = G(len(names), edges)
    J1, J2 = ix['J1'], ix['J2']
    n1 = [x for x in g.nbrs(J1) if x != J2]
    n2 = [x for x in g.nbrs(J2) if x != J1]
    adj = J2 in g.nbrs(J1)
    for v in range(len(names)):
        assert v in (J1, J2) or g.deg(v) == 4, (names[v], g.deg(v))
    g.remove_vertex(J1); g.remove_vertex(J2)
    if adj:  # vine (V): path p1-J1-J2-p2, replace by one bond p1-p2
        assert len(n1) == 1 and len(n2) == 1
        g.m[norm((n1[0], n2[0]))] += 1
    else:
        assert len(n1) == 2 and len(n2) == 2
        g.m[norm(tuple(n1))] += 1
        g.m[norm(tuple(n2))] += 1
    return g

def vine_closures(maxatoms, m_min_II):
    out = {}
    # vine (II) with m rungs
    for m in range(m_min_II, maxatoms // 2 + 1):
        names = ['J1', 'J2'] + [f'r{i}{s}' for i in range(m) for s in 'ab']
        ix = {u: i for i, u in enumerate(names)}
        E = [('J1', 'r0a'), ('J1', 'r0b'), (f'r{m-1}a', 'J2'), (f'r{m-1}b', 'J2')]
        for i in range(m):
            E += [(f'r{i}a', f'r{i}b')] * 2
            if i: E += [(f'r{i-1}a', f'r{i}a'), (f'r{i-1}b', f'r{i}b')]
        g = closure(names, ix, [(ix[a], ix[b]) for a, b in E])
        if len(g.vertices()) <= maxatoms:
            out.setdefault(canon(g), f'II(m={m})')
    for name, (spec, dashed) in VINES.items() if False else [(k, v) for k, v in VINES.items() if v]:
        for ks in itertools.product(range(maxatoms // 2 + 1), repeat=len(dashed)):
            names, ix, E = build(spec, dashed, ks)
            if len(names) - 2 > maxatoms: continue
            g = closure(names, ix, E)
            out.setdefault(canon(g), f'{name}{ks}')
    return out

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    vc2 = vine_closures(N, 2)   # figure reading: vine (II) has m >= 2 rungs
    vc1 = vine_closures(N, 1)   # E3 reading: m >= 1
    # sanity: every vine closure reduces to Q or T?
    for c, d in sorted(vc1.items(), key=lambda x: x[0][0]):
        pass
    fam = inverse_family(N)
    print(f'atoms <= {N}: {len(fam)} molecules reach Q/T by <=2 inverse (Y) sequences;'
          f' {len(vc2)} vine closures (m>=2), {len(vc1)} (m>=1)')
    # check the vine closures reduce to Q/T
    bad = []
    for c, d in vc1.items():
        pass
    miss2 = [(c, d) for c, (g, d) in fam.items() if c not in vc2]
    miss1 = [(c, d) for c, (g, d) in fam.items() if c not in vc1]
    print('NOT vine closures (figure reading, m>=2):')
    for c, d in sorted(miss2, key=lambda x: x[0][0]):
        print('  atoms', c[0], d)
    print('NOT vine closures (E3 reading, m>=1):')
    for c, d in sorted(miss1, key=lambda x: x[0][0]):
        print('  atoms', c[0], d)
    unreached = [d for c, d in vc1.items() if c not in fam]
    print('vine closures NOT reached by the inverse enumeration:', unreached)
