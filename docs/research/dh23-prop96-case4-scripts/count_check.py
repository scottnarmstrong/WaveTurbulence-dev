"""Sanity checks for the explicit decoration family of NOTE.md Lemma 4.1 (T-block component, gamma <= 1/2) and its
extension to the necklace N_m (Lemma 4.3).  Exact rational arithmetic on random lattice points of Z_L^d (d = 3).

Checks, for random (x, x', p, q) in the quarter balls around the chosen centres and r = e_1/L:
  * vector constraints at e, g, f, b, b' (c_e = c_g = c_f = 0, c_b = r, c_b' = -r);
  * Gamma_e + Gamma_g + Gamma_f + Gamma_b + Gamma_b' = 0 and Gamma_e = 2 (p-x).(p-x');
  * |Gamma_b - beta_b| <= |r|/2 and |Gamma_b' - beta_b'| <= |r|/2 with beta at the centre values (so the beta-atom
    constraints of width delta^{-1} L^{-2 gamma} hold automatically when |r| <= 2 delta^{-1} L^{-2gamma});
  * every opposite-direction pair at e, g, f has |difference| >= 8 (so LG holds for every L);
  * every bond vector stays within distance 1 of its centre (the unit-ball restriction k_l^0).
Usage: python3 -I count_check.py
"""
import random
from fractions import Fraction as F

d = 3
def vec(*a): return tuple(F(t) for t in a) + tuple(F(0) for _ in range(d - len(a)))
def add(u, v): return tuple(a + b for a, b in zip(u, v))
def sub(u, v): return tuple(a - b for a, b in zip(u, v))
def dot(u, v): return sum(a * b for a, b in zip(u, v))
def nrm2(u): return dot(u, u)
def nrm(u): return float(nrm2(u)) ** 0.5

E1, E2, E3 = vec(1), vec(0, 1), vec(0, 0, 1)
def sc(c, u): return tuple(F(c) * a for a in u)
X0, XP0, P0, Q0 = vec(0), sc(10, E1), sc(10, E2), sc(10, E3)

def rand_in_ball(c, rad, L):
    while True:
        n = tuple(random.randint(-int(rad * L), int(rad * L)) for _ in range(d))
        w = tuple(F(t, L) for t in n)
        if nrm(w) <= rad: return add(c, w)

def one(L):
    r = sc(F(1, L), E1)
    x, xp, p, q = (rand_in_ball(c, 0.25, L) for c in (X0, XP0, P0, Q0))
    S = add(x, xp)
    pp, qp = sub(S, p), sub(S, q)
    y, yp = sub(x, r), add(xp, r)
    # vector constraints (out - in)
    assert add(p, pp) == S                       # e: out p+p', in x+x'
    assert add(q, qp) == add(p, pp)              # g
    assert add(y, yp) == add(q, qp)              # f: out y+y', in q+q'
    assert sub(x, y) == r and sub(xp, yp) == sc(-1, r)
    Ge = nrm2(p) + nrm2(pp) - nrm2(x) - nrm2(xp)
    Gg = nrm2(q) + nrm2(qp) - nrm2(p) - nrm2(pp)
    Gf = nrm2(y) + nrm2(yp) - nrm2(q) - nrm2(qp)
    Gb = nrm2(x) - nrm2(y)
    Gbp = nrm2(xp) - nrm2(yp)
    assert Ge + Gg + Gf + Gb + Gbp == 0
    assert Ge == 2 * dot(sub(p, x), sub(p, xp))
    assert Ge + Gg == 2 * dot(sub(q, x), sub(q, xp))
    beta_b = 2 * dot(X0, r) - nrm2(r); beta_bp = -2 * dot(XP0, r) - nrm2(r)
    assert abs(Gb - beta_b) <= nrm(r) / 2 + 1e-12 and abs(Gbp - beta_bp) <= nrm(r) / 2 + 1e-12
    centres = {'x': (x, X0), "x'": (xp, XP0), 'p': (p, P0), "p'": (pp, sub(add(X0, XP0), P0)), 'q': (q, Q0),
               "q'": (qp, sub(add(X0, XP0), Q0)), 'y': (y, X0), "y'": (yp, XP0)}
    assert all(nrm(sub(a, c)) <= 1 for a, c in centres.values())
    pairs = [(x, p), (x, pp), (xp, p), (xp, pp), (p, q), (p, qp), (pp, q), (pp, qp), (q, y), (q, yp), (qp, y), (qp, yp)]
    assert min(nrm(sub(a, b)) for a, b in pairs) >= 8
    return True

if __name__ == '__main__':
    random.seed(20261104)
    for L in (8, 64, 1000, 10**6):
        for _ in range(2000): one(L)
        print(f'L={L}: 2000 random decorations: vector constraints, Gamma identities, automatic beta-atom constraints '
              f'(|Gamma_b - beta_b| <= |r|/2), LG margins >= 8, unit-ball restriction: all OK')
