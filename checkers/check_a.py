#!/usr/bin/env python3
"""Checker A: BGMV conditions 1-3 for a not-necessarily-simple n-Venn dual given as a plane subgraph of Q_n.

Input JSON: {"n": n, "edges": [[u, v, ...], ...], "faces": [{"vertices": [...]}, ...]} (Seamons's schema;
extra keys ignored). The faces are oriented vertex cycles. We check:
  0. every edge joins two vertices differing in exactly one bit; no repeated edges;
  1. all 2^n vertices present;
  2. the faces define an oriented embedding: every edge is traversed exactly once in each direction over all
     faces; the rotation system those faces induce is consistent (each vertex's corners form one cycle); the
     graph is connected and V - E + F = 2 (so the embedding is on the sphere); each face is a simple cycle of even
     length 2l, 2 <= l <= n, with exactly two edges of each of l distinct directions;
  3. for every direction j, the subgraphs induced by {x : j in x} and {x : j not in x} are connected.
Prints the number of crossings (= faces) and PASS/FAIL with reasons.
"""
import json, sys
from collections import defaultdict, Counter


def check(d):
    n = int(d['n'])
    N = 1 << n
    errs = []
    E = set()
    adj = defaultdict(set)
    for e in d['edges']:
        u, v = int(e[0]), int(e[1])
        x = u ^ v
        if not (0 <= u < N and 0 <= v < N) or x == 0 or x & (x - 1):
            errs.append(f'edge {u}-{v} is not a hypercube edge')
            continue
        k = (min(u, v), max(u, v))
        if k in E:
            errs.append(f'repeated edge {k}')
        E.add(k)
        adj[u].add(v); adj[v].add(u)
    # 1
    if len(adj) != N:
        errs.append(f'only {len(adj)} of {N} vertices have edges')
    # 2: darts
    darts = Counter()
    faces = [list(map(int, f['vertices'])) for f in d['faces']]
    nxt_at = {}   # (v, incoming from u) -> outgoing to w : corner map, used to check rotation consistency
    for fi, f in enumerate(faces):
        L = len(f)
        if len(set(f)) != L:
            errs.append(f'face {fi} is not a simple cycle')
        dirs = Counter()
        for i in range(L):
            a, b = f[i], f[(i + 1) % L]
            darts[(a, b)] += 1
            x = a ^ b
            if (min(a, b), max(a, b)) not in E:
                errs.append(f'face {fi} uses non-edge {a}-{b}')
            dirs[x.bit_length() - 1] += 1
            c = f[(i + 2) % L]
            nxt_at[(b, a)] = c
        l = len(dirs)
        if L % 2 or not (2 <= l <= n) or any(c != 2 for c in dirs.values()) or L != 2 * l:
            errs.append(f'face {fi} (length {L}) is not direction-balanced: {dict(dirs)}')
    for (u, v) in E:
        if darts[(u, v)] != 1 or darts[(v, u)] != 1:
            errs.append(f'edge {u}-{v} dart counts {darts[(u, v)]},{darts[(v, u)]}')
    if sum(darts.values()) != 2 * len(E):
        errs.append('faces use darts outside the edge set')
    # rotation: at each vertex v the map (incoming neighbour u) -> (outgoing neighbour c) must be one cycle
    for v in adj:
        nb = adj[v]
        seen, u = set(), next(iter(nb))
        for _ in range(len(nb)):
            seen.add(u)
            # corner at v between edge (u,v) and (v,c): next neighbour around v is c
            u = nxt_at.get((v, u))
            if u is None:
                break
        if seen != nb:
            errs.append(f'vertex {v}: corners do not form one rotation cycle')
    # connectivity and Euler
    def connected(vs):
        vs = set(vs)
        if not vs:
            return True
        start = next(iter(vs)); st = [start]; seen = {start}
        while st:
            a = st.pop()
            for b in adj[a]:
                if b in vs and b not in seen:
                    seen.add(b); st.append(b)
        return seen == vs
    if not connected(range(N)):
        errs.append('graph not connected')
    V, Ec, F = N, len(E), len(faces)
    if V - Ec + F != 2:
        errs.append(f'Euler characteristic {V - Ec + F} != 2')
    # 3
    for j in range(n):
        ins = [x for x in range(N) if x >> j & 1]
        out = [x for x in range(N) if not x >> j & 1]
        if not connected(ins) or not connected(out):
            errs.append(f'curve {j}: a half is disconnected')
    return n, F, errs


def main():
    d = json.load(open(sys.argv[1]))
    n, F, errs = check(d)
    print(f'n={n} crossings(faces)={F} edges={len(d["edges"])}')
    if errs:
        print('FAIL'); [print('  ', e) for e in errs[:30]]
        sys.exit(1)
    print('PASS')


if __name__ == '__main__':
    main()
