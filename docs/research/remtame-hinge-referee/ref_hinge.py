"""Referee re-derivation of the hinge-v3 counterexample (research-damaged NOTES 3.2).

Independent code (no import from, no copy of, check_damaged.py).  Run: python3 -I ref_hinge.py

Conventions re-derived from the sources:
  DH23 Def 4.2 (Revision_Submit.tex L637-640) = TARGET defcplmol (L1297):
    PC bond: parent -> child if the child has sign -, child -> parent if the child has sign +; it carries k_child.
    LP bond: from the atom whose paired leaf child has sign - to the atom whose paired leaf child has sign +;
             it carries the common leaf momentum.
  DH23 defdec (L458): k_n = k_{n1} - k_{n2} + k_{n3}; a node of sign z has children of signs (z, -z, z).
  DH23 decmole (L655): sum_{l at v} zeta_{v,l} k_l = c_v, zeta = +1 outgoing; c_v = 0 at degree 4,
    c_v = +k if (out,in) = (2,1), -k if (out,in) = (1,2).
  Gap of an opposite pair (x incoming, y outgoing) at v: k_x - k_y (TARGET defdiff L1940).
"""
import itertools
import random
import sys

random.seed(20261105)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  FAIL:", msg)
    return cond


# ---------------------------------------------------------------- the couple
SPEC = {  # node: (children) ; leaves are names absent from SPEC
    'P': ['x', 'm', 'u1'], 'u1': ['u11', 'u0', 'u2'], 'u2': ['u21', 'u22', 'u23'], 'u21': ['y1', 'y2', 'y3'],
    'Q': ['q1', 'q2', 'Q2'], 'Q2': ['r1', 'r2', 'r3'],
}
ROOTSIGN = {'P': +1, 'Q': -1}
PAIRS = [('u23', 'u0'), ('y1', 'm'), ('x', 'r3'), ('u11', 'q1'), ('r2', 'u22'), ('q2', 'y2'), ('y3', 'r1')]
VARS = 'ABCDEFG'  # pair i carries free momentum VARS[i]


def build_tree_data(spec, rootsign):
    sign, parent = {}, {}

    def walk(n, z):
        sign[n] = z
        if n in spec:
            for i, c in enumerate(spec[n]):
                parent[c] = n
                walk(c, z if i != 1 else -z)
    for r, z in rootsign.items():
        walk(r, z)
    return sign, parent


def vec(nvar, i=None):
    v = [0] * nvar
    if i is not None:
        v[i] = 1
    return tuple(v)


def vadd(a, b, s=1):
    return tuple(x + s * y for x, y in zip(a, b))


def momenta(spec, rootsign, pairs):
    """symbolic momenta: vectors of integer coefficients over the pair variables"""
    sign, parent = build_tree_data(spec, rootsign)
    nv = len(pairs)
    k = {}
    for i, (a, b) in enumerate(pairs):
        k[a] = vec(nv, i)
        k[b] = vec(nv, i)

    def mom(n):
        if n in k:
            return k[n]
        c1, c2, c3 = spec[n]
        k[n] = vadd(vadd(mom(c1), mom(c2), -1), mom(c3))
        return k[n]
    for n in spec:
        mom(n)
    return k, sign, parent


def molecule(spec, rootsign, pairs):
    """returns atoms, bonds = list of (tail, head, kvec, label)"""
    k, sign, parent = momenta(spec, rootsign, pairs)
    atoms = sorted(spec)
    bonds = []
    for n in spec:
        if n in parent:  # PC bond with parent
            p = parent[n]
            if sign[n] < 0:
                bonds.append((p, n, k[n], 'PC:' + n))
            else:
                bonds.append((n, p, k[n], 'PC:' + n))
    for a, b in pairs:
        pa, pb = parent[a], parent[b]
        check(sign[a] == -sign[b], 'paired leaves of opposite signs %s %s' % (a, b))
        neg, pos = (pa, pb) if sign[a] < 0 else (pb, pa)
        bonds.append((neg, pos, k[a], 'LP:%s-%s' % (a, b)))
    return atoms, bonds, k, sign, parent


def deg(bonds, v):
    return sum((b[0] == v) + (b[1] == v) for b in bonds)


def outd(bonds, v):
    return sum(b[0] == v for b in bonds)


def ind(bonds, v):
    return sum(b[1] == v for b in bonds)


def comps(atoms, bonds):
    adj = {a: set() for a in atoms}
    for b in bonds:
        adj[b[0]].add(b[1]); adj[b[1]].add(b[0])
    seen, out = set(), []
    for a in atoms:
        if a in seen:
            continue
        st, cur = [a], set()
        while st:
            x = st.pop()
            if x in cur:
                continue
            cur.add(x); st.extend(adj[x] - cur)
        seen |= cur
        out.append(frozenset(cur))
    return out


def mult(bonds, a, b):
    return sum(1 for t, h, *_ in bonds if {t, h} == {a, b})


def opp_pairs(bonds, v):
    """(i_in, j_out) bond indices of opposite-direction pairs at v"""
    ins = [i for i, b in enumerate(bonds) if b[1] == v]
    outs = [j for j, b in enumerate(bonds) if b[0] == v]
    return [(i, j) for i in ins for j in outs]


def blocks(atoms, bonds):
    """DH23 defblock L712: atom set with all induced degrees 4 except two joints with induced (in,out) = (1,1)."""
    res = []
    for r in range(2, len(atoms) + 1):
        for S in itertools.combinations(atoms, r):
            Sset = set(S)
            inner = [b for b in bonds if b[0] in Sset and b[1] in Sset]
            if len(comps(list(S), inner)) != 1:
                continue
            joints = []
            ok = True
            for a in S:
                io = (ind(inner, a), outd(inner, a))
                if io == (1, 1):
                    joints.append(a)
                elif io != (2, 2):
                    ok = False
            if ok and len(joints) == 2:
                res.append((S, tuple(joints)))
    return res


def hyperblocks(atoms, bonds):
    res = []
    for r in range(2, len(atoms) + 1):
        for S in itertools.combinations(atoms, r):
            Sset = set(S)
            inner = [b for b in bonds if b[0] in Sset and b[1] in Sset]
            for idx, b in enumerate(inner):
                rest = inner[:idx] + inner[idx + 1:]
                if len(comps(list(S), rest)) != 1:
                    continue
                joints = [a for a in S if (ind(rest, a), outd(rest, a)) == (1, 1)]
                others = all((ind(rest, a), outd(rest, a)) == (2, 2) for a in S if a not in joints)
                if others and len(joints) == 2 and {b[0], b[1]} == set(joints):
                    res.append((S, tuple(joints)))
    return res


print("== H1: the couple, its molecule M(Q_sk), blocks, skeleton")
atoms, bonds, kk, sign, parent = molecule(SPEC, ROOTSIGN, PAIRS)
nv = len(PAIRS)
check(len(atoms) == 6 and len(bonds) == 11, 'M(Q_sk): 6 atoms and 11 = 2n-1 bonds')
degs = {a: (deg(bonds, a), ind(bonds, a), outd(bonds, a)) for a in atoms}
print("  degrees (deg,in,out):", degs)
check(all(i <= 2 and o <= 2 for _, i, o in degs.values()), 'caps in/out <= 2')
check(sorted(d for d, _, _ in degs.values()) == [3, 3, 4, 4, 4, 4], 'two degree-3 atoms, rest degree 4')
check(all(b[0] != b[1] for b in bonds), 'no self-loop')
mults = {frozenset((a, b)): mult(bonds, a, b) for a, b in itertools.combinations(atoms, 2) if mult(bonds, a, b)}
check(max(mults.values()) <= 2, 'no triple bond')
dbl = [tuple(sorted(s)) for s, m in mults.items() if m == 2]
print("  double bonds:", dbl)
check(dbl == [('u1', 'u2')], 'unique double bond u1<->u2')
dbb = [b for b in bonds if {b[0], b[1]} == {'u1', 'u2'}]
check({(b[0], b[1]) for b in dbb} == {('u1', 'u2'), ('u2', 'u1')}, 'double bond has opposite directions')
check(len(comps(atoms, bonds)) == 1, 'connected')
# conservation, symbolic
kroot = kk['P']
check(kk['P'] == kk['Q'], 'root condition k_P = k_Q holds identically')
for a in atoms:
    s = vec(nv)
    for t, h, kv, _ in bonds:
        if t == a:
            s = vadd(s, kv)
        if h == a:
            s = vadd(s, kv, -1)
    d0, i0, o0 = degs[a]
    want = vec(nv) if d0 == 4 else (kroot if o0 == 2 else tuple(-x for x in kroot))
    check(s == want, 'conservation at %s' % a)
B = blocks(atoms, bonds)
HB = hyperblocks(atoms, bonds)
print("  blocks:", B, " hyper-blocks:", HB)
check(B == [(('u1', 'u2'), ('u1', 'u2'))] and HB == [], 'only block = {u1,u2}; no hyper-block')
# (CL) vine (I-a): u2 is the left/right child of u1, its 'u23' (other child of u2's sign) paired with u1's middle child
check(SPEC['u1'].index('u2') in (0, 2), 'u2 is a left/right child of u1')
mid = SPEC['u1'][1]
partner = {a: b for p in PAIRS for a, b in (p, p[::-1])}
u2ch = SPEC['u2']
same_sign = [c for c in u2ch if sign[c] == sign['u2']]
u23 = [c for c in same_sign if partner.get(c) == mid]
check(len(u23) == 1, "exactly one child of u2 with u2's sign is paired with u1's middle child (vine I-a)")


def desc(n):
    out = {n}
    for c in SPEC.get(n, []):
        out |= desc(c)
    return out


u21_, u22_ = [c for c in u2ch if c not in u23 and sign[c] > 0][0], [c for c in u2ch if sign[c] < 0][0]
GB = desc('u1') - desc('u11') - desc(u21_) - desc(u22_)
leavesGB = [x for x in GB if x not in SPEC]
check(all(partner[x] in leavesGB for x in leavesGB), 'G[B] = {u1,u0,u2,u23}: its leaves are completely paired (CL block)')
print("  G[B] =", sorted(GB), "; joint degrees", degs['u1'][0] + degs['u2'][0], "> 6: non-root VC")
check(degs['u1'][0] + degs['u2'][0] > 6, 'non-root (CL) block')
# skeleton = prime: no (1,1)-mini couple and no mini tree, no sibling pair
sib = [(a, b) for a, b in PAIRS if parent[a] == parent[b]]
check(not sib, 'no siblings paired')
mini_couple = []
for n1, n2 in itertools.combinations(SPEC, 2):
    if all(c not in SPEC for c in SPEC[n1] + SPEC[n2]):
        cross = sum(1 for a, b in PAIRS if {parent[a], parent[b]} == {n1, n2})
        if cross == 3:
            mini_couple.append((n1, n2))
mini_tree = []
for n in SPEC:
    for c in SPEC[n]:
        if c in SPEC:
            lv = [x for x in SPEC[n] if x not in SPEC] + [x for x in SPEC[c] if x not in SPEC]
            if len(lv) == 5 and sum(1 for a, b in PAIRS if a in lv and b in lv) == 2:
                mini_tree.append((n, c))
check(not mini_couple and not mini_tree, 'prime: no (1,1)-mini couple, no mini tree (so Q = Q_sk)')

print("== H2: splicing at the garden level, M_sb, hinge pairs")
# Prop block_clcn (2): remove G[B] \ {u1}; u11, u21, u22 become the children of u1; u11 keeps its position, the
# others are placed by sign (u1 has sign +: pattern (+,-,+), so the middle child is the - child u22).
spec_sb = {n: list(c) for n, c in SPEC.items() if n not in ('u2',)}
pos11 = SPEC['u1'].index('u11')
newch = [None, None, None]
newch[pos11] = 'u11'
rest = [i for i in range(3) if newch[i] is None]
for i in rest:
    newch[i] = u22_ if i == 1 else u21_
spec_sb['u1'] = newch
pairs_sb = [p for p in PAIRS if 'u0' not in p]
atoms_sb, bonds_sb, k_sb, sign_sb, parent_sb = molecule(spec_sb, ROOTSIGN, pairs_sb)
print("  u1 children in G_sb:", newch)
check(len(atoms_sb) == 5 and len(bonds_sb) == 9, 'M_sb: 5 atoms, 9 = 2n-1 bonds')
check(len(comps(atoms_sb, bonds_sb)) == 1, 'M_sb connected')
# compare with merging u1,u2 in M(Q_sk): drop the block bonds, rename u2 -> u1.  Express pair vars of M_sb in
# the M_sk variable set (pair index map), the vine-internal pair A no longer occurs.
idx_map = [PAIRS.index(p) for p in pairs_sb]


def lift(v):
    out = [0] * nv
    for i, c in enumerate(v):
        out[idx_map[i]] = c
    return tuple(out)


merged = sorted(((('u1' if t == 'u2' else t), ('u1' if h == 'u2' else h), kv) for t, h, kv, _ in bonds
                 if {t, h} != {'u1', 'u2'}))
spliced = sorted((t, h, lift(kv)) for t, h, kv, _ in bonds_sb)
check(merged == spliced, 'M(G_sb) = M(Q_sk) with the block {u1,u2} merged (same bonds and momenta)')
H = 'u1'  # the hinge atom of M_sb
# designated pairs at h: the two bonds at one joint of U = {u1,u2} in M(Q_sk) that are not in U
ext = {j: [b for b in bonds if j in b[:2] and {b[0], b[1]} != {'u1', 'u2'}] for j in ('u1', 'u2')}
des = []
for j in ('u1', 'u2'):
    bi = [b for b in ext[j] if b[1] == j][0]
    bo = [b for b in ext[j] if b[0] == j][0]
    des.append((bi[3], bo[3]))
print("  designated pairs (in, out) at h:", des)
lab_sb = {b[3]: i for i, b in enumerate(bonds_sb)}
pairs_h = opp_pairs(bonds_sb, H)
names = lambda pr: (bonds_sb[pr[0]][3], bonds_sb[pr[1]][3])
cross = [names(p) for p in pairs_h if names(p) not in des]
print("  crossing pairs at h:", cross)
gapsym = lambda pr: lift(vadd(bonds_sb[pr[0]][2], bonds_sb[pr[1]][2], -1))
Dm = vadd(vec(nv, 3), vec(nv, 4), -1)  # D - E
for p in pairs_h:
    g = gapsym(p)
    isDE = any(g == tuple(c * x for x in Dm) for c in (1, -1))
    print("   pair", names(p), "gap =", ' '.join('%+d%s' % (c, VARS[i]) for i, c in enumerate(g) if c),
          "| proportional to D-E:", isDE)
    check(isDE == (names(p) in cross), 'crossing pairs (and only they) have gap +-(D-E)')
rsym = gapsym([p for p in pairs_h if names(p) == des[0]][0])
# no gap of M(Q_sk) is proportional to D - E (so D = E creates no degenerate atom there)
allsk = []
for a in atoms:
    for i, j in opp_pairs(bonds, a):
        g = vadd(bonds[i][2], bonds[j][2], -1)
        allsk.append((a, bonds[i][3], bonds[j][3], g))
        check(not any(g == tuple(c * x for x in Dm) for c in (1, -1)) and any(g),
              'M(Q_sk) gap at %s (%s,%s) not identically 0 on D=E' % (a, bonds[i][3], bonds[j][3]))
print("  M(Q_sk) has", len(allsk), "opposite pairs; none is a multiple of D-E")

print("== H3: decorations (random family) on the slice D = E")
Lexp, gam, eta, d = 8, 0.6, 0.01, 3
Lval = 10 ** Lexp
thr = Lval ** (1 - gam + eta)  # SG threshold in units of 1/L
print("  L = 1e%d, gamma = %g, eta = %g, d = %d, SG threshold (units 1/L) = %.1f" % (Lexp, gam, eta, d, thr))


def kind(g):
    n2 = sum(x * x for x in g)
    if n2 == 0:
        return 'ZG'
    return 'SG' if n2 <= thr * thr else 'LG'


def evalv(sym, vals):
    return tuple(sum(c * vals[i][t] for i, c in enumerate(sym)) for t in range(d))


def rnd(big):
    return tuple(random.randint(-big, big) for _ in range(d))


def directed_triangles(atoms_, bonds_):
    """directed 3-cycles: triples of bond indices (l0: t0->t1, l1: t1->t2, l2: t2->t0)"""
    out = []
    for i, j, k_ in itertools.permutations(range(len(bonds_)), 3):
        a, b, c = bonds_[i], bonds_[j], bonds_[k_]
        if a[1] == b[0] and b[1] == c[0] and c[1] == a[0] and len({a[0], b[0], c[0]}) == 3:
            if min(i, j, k_) == i:  # one rotation per cycle
                out.append((i, j, k_))
    return out


def eligible_rotations(bonds_, kv, tri):
    """for each choice of v3, report (v1,v2,v3, kinds at v1,v2,v3); kinds of the triangle pair (in, out) at each atom"""
    i, j, k_ = tri
    # atom t1 = head of i: in i, out j ; t2 = head of j: in j, out k ; t0 = head of k: in k, out i
    at = [(bonds_[k_][1], k_, i), (bonds_[i][1], i, j), (bonds_[j][1], j, k_)]
    kinds = [(a, kind(vadd(kv[x], kv[y], -1))) for a, x, y in at]
    res = []
    for r in range(3):
        v1, v2, v3 = kinds[r], kinds[(r + 1) % 3], kinds[(r + 2) % 3]
        res.append((v1, v2, v3))
    return res


ntrial = 300
stats = {'ok': 0}
for trial in range(ntrial):
    big = Lval // 10
    sm = int(thr // 3)
    vals = [None] * nv
    F = rnd(big); s = rnd(sm); r = rnd(sm)
    if not any(s) or not any(r):
        continue
    Dv = rnd(big)
    vals[3] = Dv; vals[4] = Dv                     # D = E
    vals[5] = F; vals[6] = vadd(F, s)              # G = F + s
    vals[1] = vadd(vadd(Dv, s, -1), r)             # B = D - s + r  (vine gap B - F + G - E = r)
    vals[0] = rnd(big); vals[2] = rnd(big)         # A, C free
    kv_sk = [evalv(b[2], vals) for b in bonds]
    # M(Q_sk): no zero gap anywhere (no degenerate atom, eps-support at every node), vine gap SG nonzero
    zero_sk = [(a, x, y) for a, x, y, g in allsk if not any(evalv(g, vals))]
    vine_gap = evalv(vadd(dbb[0][2], dbb[1][2], -1), vals)
    kv_sb = [evalv(lift(b[2]), vals) for b in bonds_sb]
    kinds_h = {names(p): kind(vadd(kv_sb[p[0]], kv_sb[p[1]], -1)) for p in pairs_h}
    tame_h = len({kv_sb[i] for i, b in enumerate(bonds_sb) if H in b[:2]}) == 1
    others_ok = True
    for a in atoms_sb:
        if a == H:
            continue
        for i, j in opp_pairs(bonds_sb, a):
            if kind(vadd(kv_sb[i], kv_sb[j], -1)) == 'ZG':
                others_ok = False
    elig = []
    for tri in directed_triangles(atoms_sb, bonds_sb):
        for v1, v2, v3 in eligible_rotations(bonds_sb, kv_sb, tri):
            if v1[1] == 'SG' and v2[1] == 'SG':
                elig.append((v1[0], v2[0], v3[0], v3[1]))
    good = (not zero_sk and kind(vine_gap) == 'SG' and all(kinds_h[x] == 'SG' for x in des)
            and all(kinds_h[x] == 'ZG' for x in cross) and not tame_h and others_ok
            and len(elig) == 1 and elig[0][2] == H and elig[0][3] == 'ZG')
    if trial == 0:
        print("  trial 0: zero gaps in M(Q_sk):", zero_sk, "; vine gap kind:", kind(vine_gap))
        print("           kinds at h:", kinds_h, "; h tame:", tame_h)
        print("           SG-SG triangle rotations in M_sb:", elig)
        dec0 = (vals, kv_sb)
    stats['ok'] += good
print("  random decorations on the slice D=E satisfying ALL of the counterexample properties: %d / %d"
      % (stats['ok'], ntrial))
check(stats['ok'] == ntrial, 'all sampled decorations on the slice realise the counterexample')

print("== H4: literal Operation 2 (cut h along its zero-gap triangle pair) versus the skip")
vals, kv_sb = dec0


class Mol:
    def __init__(self, bonds_, kv):
        self.b = [[t, h] for t, h, *_ in bonds_]
        self.lab = [x[3] for x in bonds_]
        self.kv = list(kv)
        self.alive = [True] * len(bonds_)
        self.cls = {a: 'eps' for a in atoms_sb}
        self.rec = {}

    def atoms(self):
        return sorted(self.cls)

    def live(self):
        return [(self.b[i][0], self.b[i][1], i) for i in range(len(self.b)) if self.alive[i]]

    def ncomp(self):
        return len(comps(self.atoms(), self.live()))

    def at(self, v):
        return [i for i in range(len(self.b)) if self.alive[i] and v in self.b[i]]

    def cut(self, v, i_in, j_out, newname):
        assert self.b[i_in][1] == v and self.b[j_out][0] == v
        before = self.ncomp()
        self.b[i_in][1] = newname
        self.b[j_out][0] = newname
        self.cls[newname] = 'x'
        after = self.ncomp()
        kindcut = 'alpha' if after == before else 'beta'
        self.rec[newname] = (i_in, j_out)
        rest = [x for x in self.at(v)]
        if len(rest) >= 2:
            ii = [x for x in rest if self.b[x][1] == v]
            oo = [x for x in rest if self.b[x][0] == v]
            if ii and oo:
                self.rec[v] = (ii[0], oo[0])
        return kindcut

    def gap(self, i, j):
        return vadd(self.kv[i], self.kv[j], -1)

    def components(self):
        return comps(self.atoms(), self.live())


def triangle_pairs():
    tri = [t for t in directed_triangles(atoms_sb, bonds_sb)]
    for t in tri:
        for v1, v2, v3 in eligible_rotations(bonds_sb, kv_sb, t):
            if v1[1] == 'SG' and v2[1] == 'SG':
                return t
    return None


T = triangle_pairs()
i, j, k_ = T
at = {bonds_sb[k_][1]: (k_, i), bonds_sb[i][1]: (i, j), bonds_sb[j][1]: (j, k_)}
# literal: cut P, u21, h along their triangle pairs, then delete the triangle
M = Mol(bonds_sb, kv_sb)
for v in ('P', 'u21', H):
    pin, pout = at[v]
    M.cut(v, pin, pout, v + '_t')
for x in (i, j, k_):
    M.alive[x] = False
for v in ('P', 'u21', H):
    del M.cls[v + '_t']
comps_after = M.components()
outer = [x for x in M.at(H)]
g_outer = M.gap([x for x in outer if M.b[x][1] == H][0], [x for x in outer if M.b[x][0] == H][0])
print("  outer half of h keeps bonds", [M.lab[x] for x in outer], "with gap", g_outer)
check(len(outer) == 2 and not any(g_outer), 'literal cut: the outer half of h is a degree-2 atom with ZERO gap')
print("  components after the literal Op 2:", [sorted(c) for c in comps_after])
check(len(comps_after) == 1, 'one component (Delta F = 0): v3 = h is a beta-atom, P, u21 alpha-atoms -> N1 fails')

# skip: Op 3 cuts P, u21, h along designated pairs, all orders and all designated choices; then Op 4 (nonzero beta)
lab2i = {bonds_sb[x][3]: x for x in range(len(bonds_sb))}


def sg_pairs(v):
    return [(a, b) for a, b in opp_pairs(bonds_sb, v) if kind(vadd(kv_sb[a], kv_sb[b], -1)) == 'SG']


desig_choices = {
    'P': sg_pairs('P'),
    'u21': sg_pairs('u21'),
    H: [(lab2i[x], lab2i[y]) for x, y in des],
}
print("  SG pairs: P", [names(p) for p in desig_choices['P']], "u21", [names(p) for p in desig_choices['u21']])
nruns, bad = 0, 0
for order in itertools.permutations(['P', 'u21', H]):
    for choice in itertools.product(*[desig_choices[v] for v in order]):
        M = Mol(bonds_sb, kv_sb)
        for v, (pin, pout) in zip(order, choice):
            kc = M.cut(v, pin, pout, v + "'")
            M.cls[v] = kc; M.cls[v + "'"] = kc
        # Op 4: nonzero-gap beta cuts at eps atoms of degree >= 3
        changed = True
        while changed:
            changed = False
            for v in [a for a in M.atoms() if M.cls[a] == 'eps']:
                if len(M.at(v)) < 3:
                    continue
                for pin in [x for x in M.at(v) if M.b[x][1] == v]:
                    for pout in [x for x in M.at(v) if M.b[x][0] == v]:
                        if not any(M.gap(pin, pout)):
                            continue
                        save = [list(b) for b in M.b]
                        kc = M.cut(v, pin, pout, v + '#')
                        if kc == 'beta':
                            M.cls[v] = 'beta'; M.cls[v + '#'] = 'beta'; changed = True
                            break
                        M.b = save; del M.cls[v + '#']
                    if changed:
                        break
                if changed:
                    break
        # checks: N1 at beta atoms of degree 2, eps LG, no triangle component with two alpha atoms
        ok = True
        for a in M.atoms():
            bs = M.at(a)
            ins = [x for x in bs if M.b[x][1] == a]; outs = [x for x in bs if M.b[x][0] == a]
            if M.cls[a] == 'beta' and len(bs) == 2 and ins and outs and not any(M.gap(ins[0], outs[0])):
                ok = False
            if M.cls[a] == 'eps':
                for x in ins:
                    for y in outs:
                        if kind(M.gap(x, y)) != 'LG':
                            ok = False
        for c in M.components():
            if len(c) == 3 and all(len(M.at(a)) == 2 for a in c) and sum(M.cls[a] == 'alpha' for a in c) >= 2:
                ok = False
        nruns += 1
        bad += (not ok)
        if nruns == 1:
            print("  skip run (first order):", order, "-> components", [sorted(c) for c in M.components()],
                  "classes", M.cls)
print("  skip runs examined: %d (all orders x designated choices); runs violating N1 / eps-LG / triangle: %d"
      % (nruns, bad))
check(bad == 0, 'skip: every run ends with N1, strict eps-LG, no 2-alpha triangle component')

print("== H5: same couple, D - E SMALL NONZERO: Op 2 is eligible and cuts the hinge along a CROSSING pair")
cnt, cnt_ok = 0, 0
for trial in range(200):
    big = Lval // 10; sm = int(thr // 3)
    vals = [None] * nv
    F = rnd(big); s = rnd(sm); r = rnd(sm); t = rnd(sm)
    if not any(s) or not any(r) or not any(t):
        continue
    Dv = rnd(big)
    vals[3] = Dv; vals[4] = vadd(Dv, t)            # E = D + t, t small nonzero
    vals[5] = F; vals[6] = vadd(F, s)
    vals[1] = vadd(vadd(vals[4], s, -1), r)        # B with vine gap B - F + G - E = r
    vals[0] = rnd(big); vals[2] = rnd(big)
    kvs = [evalv(lift(b[2]), vals) for b in bonds_sb]
    elig = []
    for tri in directed_triangles(atoms_sb, bonds_sb):
        for v1, v2, v3 in eligible_rotations(bonds_sb, kvs, tri):
            if v1[1] == 'SG' and v2[1] == 'SG' and v3[1] != 'ZG':
                elig.append((v1[0], v2[0], v3[0]))
    cnt += 1
    # every eligible rotation is a rotation of the triangle {P, u21, h}; whichever atom plays v3, Op 2 cuts all
    # three atoms along their triangle pairs, so h is cut along its triangle pair
    if elig and all(set(e) == {'P', 'u21', H} for e in elig):
        cnt_ok += 1
    if trial == 0:
        print("  trial 0 eligible rotations (v1, v2, v3):", elig)
print("  decorations with t = E - D small nonzero: triangle {P,u21,h} Op-2 eligible in %d / %d" % (cnt_ok, cnt))
print("  its pair at h is", cross[0], "or", cross[1], "-- a crossing pair, never a designated pair", des)
check(cnt_ok == cnt, 'hinge v3 with nonzero crossing gap is Op-2 eligible (G3 DesRec fails for the run)')

print()
print("RESULT:", "ALL CHECKS PASSED" if not FAIL else "FAILURES: %d" % len(FAIL))
sys.exit(1 if FAIL else 0)
