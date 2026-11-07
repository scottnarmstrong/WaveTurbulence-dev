"""Referee checks for research-damaged items 2-6 (independent code; no import from / copy of check_damaged.py).

Run: python3 -I ref_cluster.py
Sections
  N  : complementary pairs at a balanced charge-0 degree-4 atom have opposite gaps (N1 breaks after a literal cut)
  C  : C0 and C1 (single-atom erasure) at graph level, and TARGET's literal case (i)/(ii) classification there
  K  : cluster lemma: pin criterion (exact rank) vs flux criterion, Delta chi = -J, J >= s+1, and a brute-force
       count check of E_pre <= N * sup E_pos on tiny molecules
  F  : Option B run on an 8-atom molecule: M_fin (before Op 5) violates finalmol's chains clause
  S  : slack inequality (cluster lemma (f)) on all feasible cluster shapes; the two excluded shapes fail
  D  : DCB closing arithmetic 2(16d+28) eta^3 <= eta under G8's smallness
"""
import itertools
import math
import random
import sys
from fractions import Fraction

random.seed(7071)
FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("  FAIL:", msg)
    return cond


# ------------------------------------------------------------------ graph helpers (bonds = list of (tail, head))
def comps(atoms, bonds):
    adj = {a: set() for a in atoms}
    for t, h in bonds:
        adj[t].add(h); adj[h].add(t)
    seen, out = set(), []
    for a in atoms:
        if a in seen:
            continue
        cur, st = set(), [a]
        while st:
            x = st.pop()
            if x not in cur:
                cur.add(x); st.extend(adj[x] - cur)
        seen |= cur; out.append(frozenset(cur))
    return out


def chi(atoms, bonds):
    return len(bonds) - len(atoms) + len(comps(atoms, bonds))


def degio(bonds, v):
    return sum(h == v for t, h in bonds), sum(t == v for t, h in bonds)


def rank(rows):
    rows = [list(map(Fraction, r)) for r in rows]
    r, ncol = 0, (len(rows[0]) if rows else 0)
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c] / rows[r][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def pinned_rank(atoms, bonds, K):
    """k0 is a function of the charges iff the homogeneous system forces k0 = 0.
    Variables: one per bond not touching K, plus k0 (last column) for all bonds touching K."""
    Kset = set(K)
    free = [i for i, (t, h) in enumerate(bonds) if t not in Kset and h not in Kset]
    col = {i: n for n, i in enumerate(free)}
    nk = len(free)
    rows = []
    for w in atoms:
        row = [0] * (nk + 1)
        for i, (t, h) in enumerate(bonds):
            z = (1 if t == w else 0) - (1 if h == w else 0)
            if z == 0:
                continue
            if i in col:
                row[col[i]] += z
            else:
                row[nk] += z
        rows.append(row)
    return rank(rows) > rank([r[:nk] for r in rows])


def pinned_flux(atoms, bonds, K):
    Kset = set(K)
    for a in K:
        i, o = degio(bonds, a)
        if i != o:
            return True
    rest = [a for a in atoms if a not in Kset]
    rb = [(t, h) for t, h in bonds if t not in Kset and h not in Kset]
    for C in comps(rest, rb):
        fl = sum(1 for t, h in bonds if t in C and h in Kset) - sum(1 for t, h in bonds if h in C and t in Kset)
        if fl != 0:
            return True
    return False


def erase(atoms, bonds, K):
    Kset = set(K)
    return [a for a in atoms if a not in Kset], [(t, h) for t, h in bonds if t not in Kset and h not in Kset]


def cluster_numbers(atoms, bonds, K):
    Kset = set(K)
    s = len(K)
    eint = sum(1 for t, h in bonds if t in Kset and h in Kset)
    e = sum(1 for t, h in bonds if (t in Kset) != (h in Kset))
    rest, rb = erase(atoms, bonds, K)
    c = sum(1 for C in comps(rest, rb) if any((t in C and h in Kset) or (h in C and t in Kset) for t, h in bonds))
    chiK = eint - s + 1
    J = (e - c) + chiK
    return s, eint, e, c, chiK, J


# ------------------------------------------------------------------ N
print("== N: balanced charge-0 degree-4 atom")
for _ in range(2000):
    ka, kc, kb = [tuple(random.randint(-50, 50) for _ in range(3)) for _ in range(3)]
    kd = tuple(a + c - b for a, c, b in zip(ka, kc, kb))       # conservation k_b + k_d = k_a + k_c
    g = lambda x, y: tuple(p - q for p, q in zip(x, y))
    neg = lambda x: tuple(-p for p in x)
    ok = g(ka, kd) == neg(g(kc, kb)) and g(ka, kb) == neg(g(kc, kd))
    if not ok:
        break
check(ok, 'complementary opposite pairs at a balanced charge-0 degree-4 atom have opposite gaps')
print("  ok (2000 random); so a zero-gap crossing triangle pair at a degree-4 hinge leaves a zero-gap outer half")

# ------------------------------------------------------------------ C
print("== C: C1 and C0 at graph level (R = 1 molecules, 2n-1 bonds)")
X = [('x2', 'x1'), ('x2', 'x1'), ('x1', 'E1'), ('E1', 'x2')]          # x1, x2: the two degree-3 atoms
Y = [('y1', 'y2'), ('y2', 'y1'), ('y1', 'y3'), ('y2', 'y3'), ('y3', 'y2'), ('E2', 'y1'), ('y3', 'E2')]


def chain(names):
    out = []
    for a, b in zip(names, names[1:]):
        out += [(a, b), (b, a)]
    return out


for label, tame in (('C1', ['E1', 'u', 'v', 'E2']), ('C0', ['E1', 'w', 'E2'])):
    bonds = X + chain(tame) + Y
    atoms = sorted({a for b in bonds for a in b})
    degs = {a: sum(degio(bonds, a)) for a in atoms}
    check(len(bonds) == 2 * len(atoms) - 1 and len(comps(atoms, bonds)) == 1, label + ': connected, 2n-1 bonds')
    check(sorted(degs.values()).count(3) == 2 and all(dv in (3, 4) for dv in degs.values()), label + ': degrees')
    check(all(max(degio(bonds, a)) <= 2 for a in atoms), label + ': caps')
    print("  %s: atoms %d, bonds %d; cluster %s pinned (rank) = %s, (flux) = %s"
          % (label, len(atoms), len(bonds), tame, pinned_rank(atoms, bonds, tame), pinned_flux(atoms, bonds, tame)))
    # R27 single-atom erasures: E1 then E2; each admits a beta-cut along its chain pair (zero gap, tame)
    cur_a, cur_b = atoms, bonds
    for e_ in ('E1', 'E2'):
        inb = [x for x in cur_b if x[1] == e_ and x[0] in tame]
        outb = [x for x in cur_b if x[0] == e_ and x[1] in tame]
        # literal beta-cut test: move the chain pair to a new atom and count components
        nb = [(t if t != e_ or (t, h) != outb[0] else e_ + "'", h if h != e_ or (t, h) != inb[0] else e_ + "'")
              for t, h in cur_b]
        bet = len(comps(cur_a + [e_ + "'"], nb)) > len(comps(cur_a, cur_b))
        # TARGET L2152 literal classification: case (i) iff deg<4 or some component of M - v has exactly one
        # atom adjacent to v
        ra, rb = erase(cur_a, cur_b, [e_])
        nbrs = {t for t, h in cur_b if h == e_} | {h for t, h in cur_b if t == e_}
        casei = sum(degio(cur_b, e_)) < 4 or any(len(C & nbrs) == 1 for C in comps(ra, rb))
        print("   %s erasing %s: beta-cut along its chain pair possible = %s; TARGET literal case = %s"
              % (label, e_, bet, '(i) cut' if casei else '(ii) erase'))
        check(bet, label + ': ' + e_ + ' admits a (zero-gap) beta-cut, so R27 item 1 erases it at Op 4')
        cur_a, cur_b = ra, rb
    left = [C for C in comps(cur_a, cur_b) if C & set(tame)]
    print("   %s after the two erasures: tame component(s) %s" % (label, [sorted(C) for C in left]))
    if label == 'C1':
        C = left[0]
        cb = [b for b in cur_b if b[0] in C]
        check(sorted(C) == ['u', 'v'] and len(cb) == 2 and chi(sorted(C), cb) == 1,
              'C1 leaves the isolated double bond {u,v} with chi = 1')
        # charges inherited: c'_u = c_u - (net of erased bonds) k0 = 0 - 0; the only constraint is k_uv = k_vu
        check(not pinned_rank(sorted(C), cb, sorted(C)), 'k0 is free in the component {u,v}: E ~ (2L+1)^d')
        gam, eta, Lexp = 0.75, 0.001, 30
        # A({u,v}) ~ L^d L^-(d-gamma) = L^gamma ; best per-component RHS: Z = 2 eps atoms of degree 2, G = 0
        print("   A({u,v}) ~ L^{%.3f} vs per-component RHS with Z=2: L^{%.4f} (fails for every gamma > 2 eta)"
              % (gam, 2 * eta))
    else:
        check([sorted(C) for C in left] == [['w']], 'C0 leaves the isolated tame atom w')
        print("   A({w}) = 1 vs TARGET R=1 (Z := 0, G = 0, rho = 1) RHS L^{-eta^5} < 1: fails; with Z = 1 it holds")

# ------------------------------------------------------------------ K
print("== K: cluster lemma on random molecules")


def random_molecule(n, p_full=0.85):
    stubs_out = {a: 2 for a in range(n)}
    stubs_in = {a: 2 for a in range(n)}
    bonds = []
    for _ in range(4 * n):
        a, b = random.randrange(n), random.randrange(n)
        if a == b or stubs_out[a] == 0 or stubs_in[b] == 0:
            continue
        if sum(1 for t, h in bonds if {t, h} == {a, b}) >= 2:
            continue
        if random.random() > p_full:
            continue
        bonds.append((a, b)); stubs_out[a] -= 1; stubs_in[b] -= 1
    return list(range(n)), bonds


def random_connected_subset(atoms, bonds, size):
    adj = {a: set() for a in atoms}
    for t, h in bonds:
        adj[t].add(h); adj[h].add(t)
    start = random.choice(atoms)
    K = {start}
    while len(K) < size:
        fr = set().union(*(adj[a] for a in K)) - K
        if not fr:
            break
        K.add(random.choice(sorted(fr)))
    return sorted(K)


nt, agree, unp, unp4, minJ = 0, 0, 0, 0, None
dchi_ok = True
for _ in range(4000):
    n = random.randint(3, 11)
    atoms, bonds = random_molecule(n)
    if not bonds:
        continue
    K = random_connected_subset(atoms, bonds, random.randint(1, max(1, n - 1)))
    pr, pf = pinned_rank(atoms, bonds, K), pinned_flux(atoms, bonds, K)
    nt += 1; agree += (pr == pf)
    s, eint, e, c, chiK, J = cluster_numbers(atoms, bonds, K)
    ra, rb = erase(atoms, bonds, K)
    dchi_ok &= (chi(ra, rb) - chi(atoms, bonds) == -J) and J >= 0
    if not pr:
        unp += 1
        if all(sum(degio(bonds, a)) == 4 for a in K):
            unp4 += 1
            minJ = (J - s) if minJ is None else min(minJ, J - s)
print("  trials %d; rank test == flux test in %d; unpinned %d; unpinned with all K-degrees 4: %d; min(J - s) = %s"
      % (nt, agree, unp, unp4, minJ))
check(agree == nt, 'pin criterion: exact rank test agrees with "unbalanced atom or nonzero flux"')
check(dchi_ok, 'Delta chi = -J with J = (e - c) + chi_K >= 0')
check(unp4 > 50 and minJ is not None and minJ >= 1, 'unpinned and all K-degrees 4  =>  J >= |K| + 1')

# brute-force count check (d = 1, box [-N, N] for every bond = the k^0 restriction; charges = parameters)
print("  brute-force E_pre <= N_K * sup E_pos on tiny molecules (d = 1, box [-1,1])")


def counts_by_charge(atoms, bonds, K, box):
    Kset = set(K)
    deg4 = {a for a in atoms if sum(degio(bonds, a)) == 4}
    tb = [i for i, (t, h) in enumerate(bonds) if t in Kset or h in Kset]
    fb = [i for i in range(len(bonds)) if i not in tb]
    cnt = {}
    k0vals = box if tb else [0]
    for k0 in k0vals:
        for vals in itertools.product(box, repeat=len(fb)):
            x = [0] * len(bonds)
            for i in tb:
                x[i] = k0
            for i, v in zip(fb, vals):
                x[i] = v
            ch = []
            ok = True
            for w in atoms:
                cw = sum(x[i] for i, (t, h) in enumerate(bonds) if t == w) - \
                    sum(x[i] for i, (t, h) in enumerate(bonds) if h == w)
                if w in deg4 and cw != 0:
                    ok = False; break
                ch.append(cw)
            if ok:
                cnt[tuple(ch)] = cnt.get(tuple(ch), 0) + 1
    return cnt


box = [-1, 0, 1]
tested, viol, needed = 0, 0, 0
for _ in range(400):
    n = random.randint(3, 6)
    atoms, bonds = random_molecule(n, p_full=0.7)
    if not (3 <= len(bonds) <= 9):
        continue
    K = random_connected_subset(atoms, bonds, random.randint(1, 2))
    pre = counts_by_charge(atoms, bonds, K, box)
    ra, rb = erase(atoms, bonds, K)
    post = counts_by_charge(ra, rb, [], box)
    if not pre:
        continue
    pin = pinned_flux(atoms, bonds, K)
    Nk = 1 if pin else len(box)
    tested += 1
    if max(pre.values()) > Nk * max(post.values()):
        viol += 1
    if not pin and max(pre.values()) > max(post.values()):
        needed += 1
print("   cases %d, violations %d; unpinned cases where the factor #k0 is really needed: %d" % (tested, viol, needed))
check(tested > 100 and viol == 0, 'E_pre(c) <= sup E_pos (pinned), <= #k0 sup E_pos (unpinned)')

# ------------------------------------------------------------------ F
print("== F: Option B on an 8-atom molecule; tame v3 = t of a skipped triangle")
B8 = {  # name: (tail, head)
    'ta': ('t', 'a'), 'bt': ('b', 't'), 'tw1': ('t', 'w1'), 'w3t': ('w3', 't'),
    'ab': ('a', 'b'), 'ao1': ('a', 'o1'), 'o2a': ('o2', 'a'), 'bo2': ('b', 'o2'), 'o1b': ('o1', 'b'),
    'o1o2': ('o1', 'o2'),
    'w1w2': ('w1', 'w2'), 'w2w1': ('w2', 'w1'), 'w1w3': ('w1', 'w3'), 'w2w3': ('w2', 'w3'), 'w3w2': ('w3', 'w2'),
}
names8 = list(B8)
atoms8 = sorted({a for b in B8.values() for a in b})
check(len(atoms8) == 8 and len(B8) == 15 and len(comps(atoms8, list(B8.values()))) == 1, 'F: 8 atoms, 15 bonds, connected')
dd = {a: degio(list(B8.values()), a) for a in atoms8}
check(all(dd[a] == (2, 2) for a in atoms8 if a not in ('o1', 'o2')) and sum(dd['o1']) == 3 == sum(dd['o2']),
      'F: o1, o2 degree 3, all others balanced degree 4')
Lexp, gam, eta, d = 8, 0.6, 0.01, 3
thr = (10 ** Lexp) ** (1 - gam + eta)
R = lambda big: tuple(random.randint(-big, big) for _ in range(d))
add = lambda *vs: tuple(sum(z) for z in zip(*vs))
neg = lambda v: tuple(-z for z in v)
big, sm = 10 ** 7, 500
k0, s = R(big), R(sm)
kv = {'ta': k0, 'bt': k0, 'tw1': k0, 'w3t': k0}
kv['ab'] = add(k0, neg(s))
kv['o2a'] = R(big); kv['ao1'] = add(kv['o2a'], s)
kv['o1b'] = R(big); kv['bo2'] = add(kv['o1b'], neg(s))
kv['o1o2'] = R(big)
p, q = R(big), R(big)
kv['w2w1'], kv['w1w2'] = p, q
kv['w1w3'] = add(k0, p, neg(q))
kv['w2w3'] = R(big)
kv['w3w2'] = add(kv['w1w3'], kv['w2w3'], neg(k0))
for a in atoms8:
    if a in ('o1', 'o2'):
        continue
    net = add(*[kv[n] for n in names8 if B8[n][0] == a], *[neg(kv[n]) for n in names8 if B8[n][1] == a])
    check(not any(net), 'F: conservation (charge 0) at ' + a)


def kindg(g):
    n2 = sum(z * z for z in g)
    return 'ZG' if n2 == 0 else ('SG' if n2 <= thr * thr else 'LG')


def pairs_at(bd, v):
    ins = [n for n in bd if bd[n][1] == v]
    outs = [n for n in bd if bd[n][0] == v]
    return [(x, y) for x in ins for y in outs]


kinds = {a: sorted({kindg(add(kv[x], neg(kv[y]))) for x, y in pairs_at(B8, a)}) for a in atoms8}
print("  pair kinds:", kinds)
check(kinds['t'] == ['ZG'] and len({kv[n] for n in names8 if 't' in B8[n]}) == 1, 'F: t is tame')
check('SG' in kinds['a'] and 'SG' in kinds['b'] and 'ZG' not in kinds['a'] + kinds['b'], 'F: a, b SG (nonzero)')
check(all(kinds[a] == ['LG'] for a in ('w1', 'w2', 'w3', 'o1', 'o2')), 'F: all other atoms LG')
# Op 1: SG blocks / hyper-blocks?  (none: list all blocks and their gaps)
bl = []
for r in range(2, 8):
    for S in itertools.combinations(atoms8, r):
        Ss = set(S)
        inner = [n for n in names8 if B8[n][0] in Ss and B8[n][1] in Ss]
        io = {a: (sum(B8[n][1] == a for n in inner), sum(B8[n][0] == a for n in inner)) for a in S}
        js = [a for a in S if io[a] == (1, 1)]
        if len(js) == 2 and all(io[a] == (2, 2) for a in S if a not in js) and \
                len(comps(list(S), [B8[n] for n in inner])) == 1:
            j = js[0]
            x = [n for n in inner if B8[n][1] == j][0]; y = [n for n in inner if B8[n][0] == j][0]
            bl.append((S, kindg(add(kv[x], neg(kv[y])))))
print("  blocks (with gap kind):", bl)

# Operation 1 collects SG VINE-LIKE objects only (vines (I)-(VIII), HV, VC, HVC; DH23 Def 8.x, Figure Vines).
# The only SG block is S6 = {a,b,t,w1,w2,w3}, joints a, b, with sigma = 1 (the bond a->b).  sigma = 1 vines are
# vines (V) only (DH23 L790), and vine (V) has at least 9 atoms (2 joints + 2 rungs + the 3-atom end, Vines.png);
# a VC of >= 2 vines has sigma = 0; S6 minus a->b is not a block (a has induced (in,out) = (1,0)), so S6 is no HV.
sgb = [S for S, kd in bl if kd == 'SG']
s6 = ('a', 'b', 't', 'w1', 'w2', 'w3')
sig = sum(1 for n in names8 if set(B8[n]) == {'a', 'b'})
check(sgb == [s6] and sig == 1 and len(s6) < 9, 'F: the only SG block has sigma = 1 and 6 < 9 atoms: not a vine-like '
      'object, so Operation 1 collects nothing')
for S, kd in bl:
    if kd != 'SG':
        print("   LG block", S, "(a vine (I), not collected)")
# Op 2: directed triangles
tris = []
for x, y, z in itertools.permutations(names8, 3):
    (a1, b1), (a2, b2), (a3, b3) = B8[x], B8[y], B8[z]
    if b1 == a2 and b2 == a3 and b3 == a1 and len({a1, a2, a3}) == 3 and min(x, y, z) == x:
        at3 = [(a2, x, y), (a3, y, z), (a1, z, x)]
        tris.append([(v, kindg(add(kv[i], neg(kv[o])))) for v, i, o in at3])
print("  directed triangles (atom, kind of triangle pair):", tris)
elig = [T for T in tris for r in range(3)
        if T[r][1] == 'SG' and T[(r + 1) % 3][1] == 'SG' and T[(r + 2) % 3][1] != 'ZG']
skipped = [T for T in tris for r in range(3)
           if T[r][1] == 'SG' and T[(r + 1) % 3][1] == 'SG' and T[(r + 2) % 3][1] == 'ZG']
check(not elig and len(skipped) == 1, 'F: no eligible triangle; one SG-SG triangle with zero-gap v3 = t (skipped)')
# Op 3: cut a, b along their (triangle) SG pairs; Op 4: nonzero-gap beta-cuts
cur = {n: list(B8[n]) for n in names8}
cls = {a: 'eps' for a in atoms8}


def ncomp(cur, cls):
    return len(comps(sorted(cls), [tuple(v) for v in cur.values()]))


for v, (pin, pout) in (('a', ('ta', 'ab')), ('b', ('ab', 'bt'))):
    before = ncomp(cur, cls)
    cur[pin][1] = v + '1'; cur[pout][0] = v + '1'
    cls[v + '1'] = 'x'
    kd_ = 'alpha' if ncomp(cur, cls) == before else 'beta'
    cls[v] = cls[v + '1'] = kd_
changed = True
while changed:
    changed = False
    for v in [a for a in sorted(cls) if cls[a] == 'eps']:
        ins = [n for n in cur if cur[n][1] == v]; outs = [n for n in cur if cur[n][0] == v]
        if len(ins) + len(outs) < 3:
            continue
        for x in ins:
            for y in outs:
                if not any(add(kv[x], neg(kv[y]))):
                    continue
                before = ncomp(cur, cls)
                cur[x][1] = v + '#'; cur[y][0] = v + '#'; cls[v + '#'] = 'beta'
                if ncomp(cur, cls) > before:
                    cls[v] = 'beta'; changed = True; break
                cur[x][1] = v; cur[y][0] = v; del cls[v + '#']
            if changed:
                break
        if changed:
            break
CC = comps(sorted(cls), [tuple(v) for v in cur.values()])
print("  M_fin components:", [sorted(c) for c in CC], " classes:", cls)
compt = [c for c in CC if 't' in c][0]
dg = {a: sum(1 for n in cur if a in cur[n]) for a in compt}
perfect = all((dg[a] == 4) if cls[a] == 'eps' else (dg[a] == 2) for a in compt)
chainK = [a for a in compt if cls[a] != 'eps']
ends = [cur[n][1] if cur[n][0] in chainK else cur[n][0] for n in cur
        if (cur[n][0] in chainK) != (cur[n][1] in chainK) and (cur[n][0] in compt)]
print("  component of t: perfect = %s; its alpha/beta chain %s attaches at %s" % (perfect, chainK, ends))
check(perfect and len(chainK) == 2 and ends == ['t', 't'],
      'F: M_fin (before Op 5) has a PERFECT component whose chain has both ends at the same eps-atom t')
nb = [a for a in cls if cls[a] == 'beta']
check(all(any(add(kv[x], neg(kv[y]))) for v in nb for x in cur for y in cur
          if cur[x][1] == v and cur[y][0] == v), 'F: N1 holds')
# Op 5: erase t
s_, eint, e_, c_, chiK, J = cluster_numbers(sorted(cls), [tuple(v) for v in cur.values()], ['t'])
print("  Op 5 on {t}: s=%d e=%d c=%d chi_K=%d J=%d pinned=%s" %
      (s_, e_, c_, chiK, J, pinned_flux(sorted(cls), [tuple(v) for v in cur.values()], ['t'])))
check(J == 2, 'F: Op 5 at t: unpinned, J = 2 = s + 1')

# ------------------------------------------------------------------ S
print("== S: slack of the cluster lemma (f) over all feasible shapes, s <= 24")


def slack(d, gam, eta, s, e, J, pinned, C0=1000.0):
    g0 = min(gam, 1 - gam)
    a = 2 * g0 + 5 * eta ** 2
    logI = -(d - gam) * J + (0 if pinned else d)
    return a * (s - J) - eta * e - C0 * eta ** 5 * (s + e) - logI


worst = (1e9, None)
nshape = 0
for d in range(3, 9):
    for gi in range(1, 100, 2):
        gam = gi / 100
        g0 = min(gam, 1 - gam)
        for eta in (g0 / (1000 * d), g0 / (1e5 * d)):
            for s in range(1, 25):
                for n3 in range(0, s + 1):                      # number of degree-3 atoms in K (pinned if > 0)
                    for chiK in range(0, 2 * s + 2):
                        eint = chiK + s - 1
                        e = 3 * n3 + 4 * (s - n3) - 2 * eint
                        if e < 0 or (s > 1 and eint < s - 1):
                            continue
                        # slack = (d - gamma - a) J + a s - ... is increasing in J = e - c + chi_K, so the worst c is
                        # the largest feasible one: c = e (pinned), c = e // 2 (unpinned: each component gets an
                        # even number >= 2 of bonds); c = 0 iff e = 0
                        for pinned in (True, False):
                            if not pinned and n3 > 0:
                                continue                # unpinned: all atoms balanced, so all degree 4
                            c = 0 if e == 0 else (e if pinned else e // 2)
                            J = e - c + chiK
                            if True:
                                nshape += 1
                                v = slack(d, gam, eta, s, e, J, pinned)
                                if v < worst[0]:
                                    worst = (v, (d, gam, eta, s, e, J, pinned))
print("  shapes evaluated %d; minimum slack %.5f at (d, gamma, eta, s, e, J, pinned) = %s" % (nshape, worst[0], worst[1]))
check(worst[0] > 0, 'slack > 0 on every feasible cluster shape')
bad1 = slack(3, 0.75, 0.25 / 3000, 1, 2, 1, False)       # unpinned degree-2 cycle atom
bad2 = slack(3, 0.75, 0.25 / 3000, 2, 0, 1, False)       # isolated tame double bond
print("  excluded shapes: degree-2 unpinned atom slack %.4f, isolated tame double bond slack %.4f" % (bad1, bad2))
check(bad1 < 0 and bad2 < 0, 'the two shapes excluded by T0 have negative slack')

# ------------------------------------------------------------------ D
print("== D: DCB closing arithmetic")
okD = True
for d in range(3, 20):
    for gi in range(501, 1000):
        gam = gi / 1000
        g0 = min(gam, 1 - gam)
        eta = min(g0 / (1000 * d), (2 * gam - 1) / (1000 * d), 1 / (4 * 1440061))
        C = 16 * d + 28
        # interpolation exponent C eta^3 (w+1) vs allowance eta w, w >= 1; alpha factor (gamma-5eta)/2 >= eta,
        # beta factor g0 + 2 eta^2 >= eta
        okD &= (2 * C * eta ** 3 <= eta) and ((gam - 5 * eta) / 2 >= eta) and (g0 + 2 * eta ** 2 >= eta)
        okD &= all(C * eta ** 3 * (w + 1) <= eta * w for w in (1, 2, 5, 100))
check(okD, 'DCB closes: 2(16d+28) eta^3 <= eta and the alpha/beta factors are >= L^eta (G8 smallness)')
print("  eta^2 <= 1/(32d+56) holds whenever d*eta <= 1/2000:", all((1 / (2000 * d)) ** 2 <= 1 / (32 * d + 56)
                                                                   for d in range(3, 1000)))

print()
print("RESULT:", "ALL CHECKS PASSED" if not FAIL else "FAILURES: %d" % len(FAIL))
sys.exit(1 if FAIL else 0)
