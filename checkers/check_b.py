#!/usr/bin/env python3
"""Checker B (independent of check_a.py): verifies a Venn dual by building the primal diagram.

Primal: one crossing per face; for each curve j, the arcs of curve j are dual to the j-edges. We check
  - every listed edge is a Q_n edge, every 2^n vertex occurs, no duplicate edges;
  - every edge borders exactly two face-sides with opposite orientation (oriented 2-cell embedding);
  - around every vertex the incident face corners close up into one disk (link of the vertex is a single cycle);
  - sphere: V - E + F == 2 and the face-adjacency (dual) graph is connected;
  - every face, read as a crossing, has 2l sides on l distinct curves, two sides per curve;
  - for each curve j, the dual arcs of the j-edges form ONE simple closed cycle through the crossings
    (every crossing on curve j has dual degree 2 for j, and the j-arcs are connected). In the plane this is
    equivalent to the j-edges forming a bond, i.e. both halves connected.
"""
import json, sys
from collections import defaultdict


def main():
    d = json.load(open(sys.argv[1]))
    n = d['n']; N = 1 << n
    bad = []
    edges = {}
    for e in d['edges']:
        u, v = sorted((e[0], e[1]))
        if bin(u ^ v).count('1') != 1:
            bad.append(f'non-cube edge {u},{v}')
        if (u, v) in edges:
            bad.append(f'duplicate {u},{v}')
        edges[(u, v)] = (u ^ v).bit_length() - 1
    verts = {x for e in edges for x in e}
    if verts != set(range(N)):
        bad.append(f'{N - len(verts)} vertices missing')
    faces = [f['vertices'] for f in d['faces']]
    side = defaultdict(list)          # undirected edge -> [(face, orientation +1/-1)]
    corners = defaultdict(list)       # vertex -> [(prev, next)] around it, one per face corner
    for fi, f in enumerate(faces):
        L = len(f)
        if len(set(f)) != L:
            bad.append(f'face {fi} repeats a vertex')
        for i in range(L):
            a, b = f[i], f[(i + 1) % L]
            side[(min(a, b), max(a, b))].append((fi, 1 if a < b else -1))
            corners[b].append((a, f[(i + 2) % L]))
        dirs = [((f[i] ^ f[(i + 1) % L]).bit_length() - 1) for i in range(L)]
        cnt = defaultdict(int)
        for x in dirs:
            cnt[x] += 1
        if L % 2 or len(cnt) * 2 != L or len(cnt) < 2 or any(c != 2 for c in cnt.values()):
            bad.append(f'face {fi}: sides {dirs} are not l curves with two sides each')
    for e in edges:
        s = side.get(e, [])
        if len(s) != 2 or s[0][1] == s[1][1]:
            bad.append(f'edge {e} sides {s}')
    if set(side) - set(edges):
        bad.append('a face uses a non-edge')
    for v, cs in corners.items():
        m = {p: q for p, q in cs}
        if len(m) != len(cs):
            bad.append(f'vertex {v}: repeated corner')
            continue
        start = cs[0][0]; x = start; k = 0
        while True:
            x = m.get(x); k += 1
            if x is None or x == start or k > len(cs):
                break
        if x != start or k != len(cs):
            bad.append(f'vertex {v}: corners are not one disk')
    V, E, F = N, len(edges), len(faces)
    if V - E + F != 2:
        bad.append(f'V-E+F = {V - E + F}')
    dual = defaultdict(set)
    for e, s in side.items():
        if len(s) == 2:
            dual[s[0][0]].add(s[1][0]); dual[s[1][0]].add(s[0][0])
    seen = {0}; st = [0]
    while st:
        a = st.pop()
        for b in dual[a]:
            if b not in seen:
                seen.add(b); st.append(b)
    if len(seen) != F:
        bad.append('dual graph disconnected')
    for j in range(n):
        arcs = [tuple(f for f, _ in side[e]) for e, dj in edges.items() if dj == j and len(side[e]) == 2]
        deg = defaultdict(int); nb = defaultdict(list)
        for a, b in arcs:
            deg[a] += 1; deg[b] += 1; nb[a].append(b); nb[b].append(a)
        if not arcs or any(c != 2 for c in deg.values()):
            bad.append(f'curve {j}: crossing degrees {sorted(set(deg.values()))}')
            continue
        start = arcs[0][0]; seen = {start}; st = [start]
        while st:
            a = st.pop()
            for b in nb[a]:
                if b not in seen:
                    seen.add(b); st.append(b)
        if len(seen) != len(deg):
            bad.append(f'curve {j}: not a single closed curve ({len(seen)} of {len(deg)} crossings)')
    print(f'n={n} crossings={F} edges={E}')
    if bad:
        print('FAIL'); [print('  ', b) for b in bad[:30]]; sys.exit(1)
    print('PASS')


if __name__ == '__main__':
    main()
