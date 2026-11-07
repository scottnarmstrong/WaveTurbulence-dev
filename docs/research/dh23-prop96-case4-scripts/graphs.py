"""Small undirected multigraph utilities: canonical form by refinement + backtracking.

A graph is (n, edges) with edges a dict {(a,b): mult} with a<b, atoms 0..n-1.
"""
from collections import Counter
from itertools import permutations

def mk(n, edgelist):
    c = Counter()
    for a, b in edgelist:
        assert a != b, (a, b)
        c[(min(a, b), max(a, b))] += 1
    return (n, dict(c))

def adj(g):
    n, E = g
    A = [[0]*n for _ in range(n)]
    for (a, b), m in E.items():
        A[a][b] += m; A[b][a] += m
    return A

def degrees(g):
    A = adj(g); return [sum(r) for r in A]

def refine(A, colors):
    n = len(A)
    while True:
        sig = [(colors[v], tuple(sorted((colors[u], A[v][u]) for u in range(n) if A[v][u]))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(colors)):
            return new
        colors = new

def canon(g):
    """Canonical form: lexicographically minimal adjacency tuple over individualization-refinement leaves."""
    n, E = g
    A = adj(g)
    best = [None]
    def rec(colors):
        colors = refine(A, colors)
        if len(set(colors)) == n:
            order = sorted(range(n), key=lambda v: colors[v])
            form = tuple(A[order[i]][order[j]] for i in range(n) for j in range(i+1, n))
            if best[0] is None or form < best[0]:
                best[0] = form
            return
        # first non-singleton cell (smallest color index)
        cnt = Counter(colors)
        target = min(c for c in cnt if cnt[c] > 1)
        for v in range(n):
            if colors[v] == target:
                nc = [2*c for c in colors]
                nc[v] = 2*target - 1
                rec(nc)
    rec([0]*n)
    return (n, best[0])

def connected(g):
    n, E = g
    A = adj(g)
    seen = {0}; st = [0]
    while st:
        v = st.pop()
        for u in range(n):
            if A[v][u] and u not in seen:
                seen.add(u); st.append(u)
    return len(seen) == n

def edges_list(g):
    n, E = g
    out = []
    for (a, b), m in sorted(E.items()):
        out += [(a, b)] * m
    return out
