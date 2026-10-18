"""Independent referee for a minimum-vertex n-Venn certificate (Claude/Venn session), v2 2026-10-17.
v2 changes from v1 (v1 kept unchanged as ref37.py): accurate docstring for check 6; an edge-list mismatch is a
failure; nonzero exit code on failure; logs argv and the SHA-256 of the input and of this script.

Input: faces = cycles of region labels (subsets of {0..7} as bitmasks) around each crossing point.
Checks, from the face cycles only:
  1. every consecutive pair in a face cycle differs in exactly one bit (adjacent regions across one curve);
  2. every directed edge occurs in exactly one face and its reverse in exactly one face (closed oriented surface);
  3. vertex links are single cycles (no pinched vertices, so each label is one region = one disk-star);
  4. connected, V - E + F = 2 (sphere);
  5. all 2^n labels occur (Venn: each subset exactly one region; distinct labels = distinct vertices, and 3 rules out
     one label standing for two regions);
  6. at each crossing of size 2k every direction occurs exactly twice (k curves pass through, each exactly once), and at
     least one pair of curves crosses there (their two positions interleave); other pairs may touch (BGMV definition:
     "in any intersection point of at least two curves, at least two of them must cross");
  7. each curve i is a single closed curve: the H-edges flipping bit i, joined through crossings, form one cycle;
  8. the region labelled 0 exists (outer region) and bit i is consistent (follows from 1,7 on the sphere).
Also: counts, face-size histogram, and comparison with the certificate's own edge list (not used for the checks).
"""
import json, sys, hashlib
from collections import defaultdict, Counter

F = sys.argv[1]
print('argv:', sys.argv)
print('input sha256:', hashlib.sha256(open(F, 'rb').read()).hexdigest())
print('script sha256:', hashlib.sha256(open(__file__, 'rb').read()).hexdigest())
d = json.load(open(F))
n = d['n']
faces = [f['vertices'] for f in d['faces']]
ok = True
def fail(msg):
    global ok
    ok = False
    print('FAIL:', msg)

def onebit(x):
    return x and not (x & (x - 1))

# 1 + 6
dedge = {}
TOUCH = [0, 0]
for fi, cyc in enumerate(faces):
    L = len(cyc)
    if L < 4 or L % 2:
        fail(f'face {fi} has length {L}')
    bits = []
    for j in range(L):
        u, v = cyc[j], cyc[(j + 1) % L]
        x = u ^ v
        if not onebit(x) or not (0 <= u < 2**n and 0 <= v < 2**n):
            fail(f'face {fi} step {j}: {u}->{v} not a one-bit step')
            bits.append(-1)
        else:
            bits.append(x.bit_length() - 1)
        if (u, v) in dedge:
            fail(f'directed edge {u}->{v} in two faces ({dedge[(u, v)][0]}, {fi})')
        dedge[(u, v)] = (fi, j)
    cnt = Counter(bits)
    if any(c != 2 for c in cnt.values()) or -1 in cnt:
        fail(f'face {fi}: some direction does not occur exactly twice: {dict(cnt)}')
    # crossing structure: curves a,b cross here iff their two positions interleave; at least one pair must cross
    pos = defaultdict(list)
    for j, b in enumerate(bits):
        pos[b].append(j)
    cross = touch = 0
    keys = sorted(pos)
    for x in range(len(keys)):
        for y in range(x + 1, len(keys)):
            a1, a2 = pos[keys[x]]; b1, b2 = pos[keys[y]]
            inter = (a1 < b1 < a2) != (a1 < b2 < a2)
            cross += inter; touch += (not inter)
    TOUCH[0] += touch; TOUCH[1] += cross
    if cross == 0:
        fail(f'face {fi}: no pair of curves crosses at this point')
# 2
for (u, v) in dedge:
    if (v, u) not in dedge:
        fail(f'directed edge {u}->{v} has no reverse')
und = {frozenset(e) for e in dedge}
V = len({x for c in faces for x in c})
E = len(und)
Fn = len(faces)
# 3 vertex links: around vertex v, from incoming edge (u->v) in face f, the next edge in f is v->w;
# the edge after that around v is the reverse w->v ... rotation: sigma(v->w) = next outgoing after taking reverse.
out_edges = defaultdict(list)
for (u, v) in dedge:
    out_edges[u].append(v)
pinched = 0
for v, outs in out_edges.items():
    # successor around v: outgoing edge v->w lies in face f at position j; the previous step in that face is p->v
    # (position j-1). The edge v->p is the next outgoing edge around v.
    succ = {}
    for w in outs:
        fi, j = dedge[(v, w)]
        cyc = faces[fi]
        p = cyc[(j - 1) % len(cyc)]
        succ[w] = p
    start = outs[0]
    seen = {start}
    x = succ[start]
    while x != start:
        if x in seen or x not in succ:
            break
        seen.add(x)
        x = succ[x]
    if len(seen) != len(outs):
        pinched += 1
if pinched:
    fail(f'{pinched} vertices have a link that is not a single cycle')
# 4 connectivity
adj = defaultdict(set)
for (u, v) in dedge:
    adj[u].add(v)
start = next(iter(adj))
stack, comp = [start], {start}
while stack:
    x = stack.pop()
    for y in adj[x]:
        if y not in comp:
            comp.add(y)
            stack.append(y)
if len(comp) != V:
    fail('dual graph not connected')
if V - E + Fn != 2:
    fail(f'Euler: V-E+F = {V}-{E}+{Fn} = {V - E + Fn}')
# 5
labels = {x for c in faces for x in c}
if labels != set(range(2**n)):
    fail(f'labels present: {len(labels)} of {2**n}')
# 7 curves: nodes = undirected H-edges flipping bit i; at each face the two edges flipping bit i are joined.
for i in range(n):
    nodes = [e for e in und if onebit(min(e) ^ max(e)) and (min(e) ^ max(e)).bit_length() - 1 == i]
    g = defaultdict(list)
    for fi, cyc in enumerate(faces):
        L = len(cyc)
        es = [frozenset((cyc[j], cyc[(j + 1) % L])) for j in range(L) if (cyc[j] ^ cyc[(j + 1) % L]).bit_length() - 1 == i]
        if len(es) == 2:
            a, b = es
            g[a].append(b)
            g[b].append(a)
    if not nodes:
        fail(f'curve {i} has no edges')
        continue
    if any(len(g[e]) != 2 for e in nodes):
        fail(f'curve {i}: some segment does not have degree 2')
    s = nodes[0]
    seen = {s}
    st = [s]
    while st:
        x = st.pop()
        for y in g[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    if len(seen) != len(nodes):
        fail(f'curve {i}: {len(nodes)} segments in more than one closed curve ({len(seen)} reachable)')
    crossings_on_i = sum(1 for c in faces if any((c[j] ^ c[(j + 1) % len(c)]).bit_length() - 1 == i for j in range(len(c))))
    print(f'curve {i}: {len(nodes)} segments, through {crossings_on_i} crossings, single closed curve: {len(seen) == len(nodes)}')
# BGMV condition 3: for each j, {x: j in x} and {x: j not in x} each induce connected subgraphs of H
for j in range(n):
    for side in (0, 1):
        S = [x for x in range(2**n) if ((x >> j) & 1) == side]
        Sset = set(S)
        seen = {S[0]}; st = [S[0]]
        while st:
            x = st.pop()
            for y in adj[x]:
                if y in Sset and y not in seen:
                    seen.add(y); st.append(y)
        if len(seen) != len(S):
            fail(f'BGMV cond 3: curve {j} side {side} not connected')
print('touching pairs at crossings:', TOUCH[0], ' crossing pairs:', TOUCH[1])
# counts and comparison with certificate edges
print('V,E,F =', V, E, Fn, ' face sizes', dict(sorted(Counter(len(c) for c in faces).items())))
cert = {frozenset((a, b)) for a, b, _ in d['edges']}
print('certificate edge list matches face-derived edges:', cert == und, len(cert))
if cert != und:
    fail('certificate edge list differs from face-derived edges')
print('RESULT:', 'PASS' if ok else 'FAIL')
sys.exit(0 if ok else 1)
