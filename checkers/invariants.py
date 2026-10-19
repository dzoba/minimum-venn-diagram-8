#!/usr/bin/env python3
"""Invariants of the certificates, as cited in the paper and README. Not a validity checker: run the three
checkers first (checkers/run_all.py). Usage, from the repository root:

    python3 checkers/invariants.py > logs/invariants.log

Conventions. A region label is an integer whose bit i (i = 0, ..., n-1) says whether the region lies inside curve
i+1; curves are numbered 1..n in the paper. A face is the cyclic list of labels around one crossing point. Two
curves cross at a point when their two edges on that face interleave (i..k..i..k), and touch otherwise.

For each certificate this prints: V, E, F, the lower bound L_n = ceil((2^n - 2)/(n - 1)); the face-length and
vertex-degree histograms; the number of points on each curve (= edges of that direction); crossing and touching
pair incidences; and the colorful faces (length 2n, containing two complementary labels; BGMV, Section 5).
For the 8-curve files it computes the full group of automorphisms x -> pi(x) XOR c of the face list (pi a
permutation of the curves), orientation preserving (faces map to faces as cyclic sequences) or reversing (faces
map to reversed faces), with the fixed labels, edges and faces of each nontrivial element.
For the 9-curve files it prints, for every curve c, the number of points it shares with each other curve
("meetings") and how many of those are crossings, and whether some curve meets every other curve exactly twice.
Finally it checks that each file of the doubling chain is the doubling of the previous one by BGMV's doubling lemma
(Lemma 10 of the SoCG 2026 version, LIPIcs 367; Lemma 11 of arXiv:2511.09230v1).
"""
import itertools
import json
import os
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(path):
    d = json.load(open(os.path.join(ROOT, path)))
    return d['n'], [list(f['vertices']) for f in d['faces']]


def bit(u, v):
    return (u ^ v).bit_length() - 1


def canon(cyc):
    L = len(cyc)
    return min(tuple(cyc[i:] + cyc[:i]) for i in range(L))


def canon_unoriented(cyc):
    return min(canon(cyc), canon(cyc[::-1]))


def pairs_at(face):
    """Map (i, k) -> True if curves i, k cross at this point, False if they touch."""
    L = len(face)
    pos = {}
    for j in range(L):
        pos.setdefault(bit(face[j], face[(j + 1) % L]), []).append(j)
    out = {}
    ks = sorted(pos)
    for x in range(len(ks)):
        for y in range(x + 1, len(ks)):
            a1, a2 = pos[ks[x]]
            b1, b2 = pos[ks[y]]
            out[(ks[x], ks[y])] = (a1 < b1 < a2) != (a1 < b2 < a2)
    return out


def basic(path):
    n, faces = load(path)
    N = 1 << n
    edges = {frozenset((f[j], f[(j + 1) % len(f)])) for f in faces for j in range(len(f))}
    deg = Counter()
    for e in edges:
        for x in e:
            deg[x] += 1
    dircount = [0] * n
    for e in edges:
        u, v = tuple(e)
        dircount[bit(u, v)] += 1
    cross = touch = 0
    for f in faces:
        for c in pairs_at(f).values():
            cross += c
            touch += not c
    colorful = []
    for i, f in enumerate(faces):
        if len(f) == 2 * n:
            s = set(f)
            ap = sorted(x for x in s if (x ^ (N - 1)) in s and x < (x ^ (N - 1)))
            if ap:
                colorful.append((i, ap))
    Ln = -(-(N - 2) // (n - 1))
    print(f'== {path}')
    print(f'  n={n}  V={len(deg)}  E={len(edges)}  F={len(faces)}  V-E+F={len(deg) - len(edges) + len(faces)}  '
          f'L_n=ceil((2^n-2)/(n-1))={Ln}  F-L_n={len(faces) - Ln}')
    print(f'  face lengths: {dict(sorted(Counter(map(len, faces)).items()))}')
    print(f'  vertex degrees: {dict(sorted(Counter(deg.values()).items()))}')
    print(f'  points on curve 1..n (= edges of each direction): {dircount}; sorted {sorted(dircount)}')
    print(f'  deficit sum_f (n - l_f) = {n * len(faces) - len(edges)}')
    print(f'  pair incidences at points: crossing {cross}, touching {touch}; '
          f'points where no pair crosses: {sum(1 for f in faces if not any(pairs_at(f).values()))}')
    print(f'  colorful faces (index, complementary pairs {{x, ~x}} with x < ~x): {colorful[:6]}'
          f'{" ..." if len(colorful) > 6 else ""} ({len(colorful)} in all)')
    return n, faces, edges


def automorphisms(n, faces, edges):
    """All maps x -> pi(x) XOR c preserving the face list, with orientation flag. pi permutes bit positions."""
    N = 1 << n
    dirc = [0] * n
    for e in edges:
        u, v = tuple(e)
        dirc[bit(u, v)] += 1
    S = {canon(f) for f in faces}
    S_rev = {canon(f[::-1]) for f in faces}
    edgeset = {tuple(sorted(e)) for e in edges}
    found = []
    for pi in itertools.permutations(range(n)):
        if any(dirc[pi[j]] != dirc[j] for j in range(n)):
            continue
        perm = [0] * N
        for x in range(N):
            y = 0
            for j in range(n):
                if x >> j & 1:
                    y |= 1 << pi[j]
            perm[x] = y
        for c in range(N):
            g = [perm[x] ^ c for x in range(N)]
            if any(tuple(sorted((g[u], g[v]))) not in edgeset for u, v in edgeset):
                continue
            img = {canon([g[x] for x in f]) for f in faces}
            if img == S:
                found.append((pi, c, '+', g))
            elif img == S_rev:
                found.append((pi, c, '-', g))
    return found


def describe_auts(n, faces, edges):
    auts = automorphisms(n, faces, edges)
    pres = sum(1 for a in auts if a[2] == '+')
    rev = len(auts) - pres
    print(f'  automorphisms x -> pi(x) XOR c of the face list: {len(auts)} '
          f'({pres} orientation preserving, {rev} reversing)')
    for pi, c, o, g in auts:
        if all(pi[j] == j for j in range(n)) and c == 0:
            continue
        cyc, seen = [], set()
        for j in range(n):
            if j in seen or pi[j] == j:
                continue
            k, cy = j, []
            while k not in seen:
                seen.add(k)
                cy.append(k + 1)
                k = pi[k]
            cyc.append('(' + ' '.join(map(str, cy)) + ')')
        fixed_labels = sum(1 for x in range(1 << n) if g[x] == x)
        fixed_edges = sorted(tuple(sorted(e)) for e in edges if {g[x] for x in e} == set(e))
        fixed_faces = [(i, len(f)) for i, f in enumerate(faces)
                       if canon_unoriented([g[x] for x in f]) == canon_unoriented(f)]
        involution = all(g[g[x]] == x for x in range(1 << n))
        print(f'    curves {"".join(cyc) or "id"} (curves 1..n), XOR {c} = 0b{c:0{n}b}; orientation {o}; '
              f'involution {involution}; fixed labels {fixed_labels}; fixed edges {fixed_edges}; '
              f'fixed faces (index, length) {fixed_faces}')
    return auts


def meetings(n, faces):
    """meet[c][j] = number of points shared by curves c and j; cr[c][j] = how many of those are crossings."""
    meet = [[0] * n for _ in range(n)]
    cr = [[0] * n for _ in range(n)]
    for f in faces:
        for (i, k), c in pairs_at(f).items():
            meet[i][k] += 1
            meet[k][i] += 1
            cr[i][k] += c
            cr[k][i] += c
    return meet, cr


def show_meetings(n, faces):
    meet, cr = meetings(n, faces)
    for c in range(n):
        others = [j for j in range(n) if j != c]
        k = sum(1 for f in faces if any(bit(f[j], f[(j + 1) % len(f)]) == c for j in range(len(f))))
        print(f'    curve {c + 1}: points on it {k}; meetings with curves {[j + 1 for j in others]}: '
              f'{[meet[c][j] for j in others]}; of which crossings {[cr[c][j] for j in others]}')
    two = [c + 1 for c in range(n) if all(meet[c][j] == 2 for j in range(n) if j != c)]
    print(f'  curves meeting every other curve in exactly 2 points: {two or "none"}')


def is_doubling(small, big):
    """Is big (n+1 curves) the BGMV doubling of small (n curves) (Lemma 10 of the SoCG version, Lemma 11 of arXiv
    v1)? Check: the faces of big that avoid direction n are the faces of small minus one colorful face O, once as they
    are and once with bit n added (each copy up to orientation), and the remaining two faces have length 2(n+1) and
    use direction n twice."""
    n, fs = load(small)
    m, fb = load(big)
    if m != n + 1 or len(fb) != 2 * len(fs):
        return False, 'sizes'
    top = 1 << n
    rest = [f for f in fb if not any(bit(f[j], f[(j + 1) % len(f)]) == n for j in range(len(f)))]
    seam = [f for f in fb if f not in rest]
    lo = Counter(canon_unoriented(f) for f in rest if all(x < top for x in f))
    hi = Counter(canon_unoriented([x ^ top for x in f]) for f in rest if all(x >= top for x in f))
    mixed = [f for f in rest if not (all(x < top for x in f) or all(x >= top for x in f))]
    small_c = Counter(canon_unoriented(f) for f in fs)
    missing_lo = small_c - lo
    ok = (not mixed and lo == hi and sum(missing_lo.values()) == 1 and not (lo - small_c)
          and len(seam) == 2 and all(len(f) == 2 * m for f in seam))
    O = next(iter(missing_lo)) if missing_lo else None
    return ok, f'omitted face of the smaller diagram has length {len(O) if O else None}'


def main():
    print('Invariants of the certificates (computed from the face lists only).\n')
    files = ['data/venn8_37_halfturn_a.json', 'data/venn8_37_halfturn_b.json',
             'calibration/venn8_39_crossing_candidate.json', 'calibration/venn8_40_source_variant030.json',
             'data/venn9_74.json', 'data/venn9_74_mixed_r2.json', 'data/venn9_74_k3_nearmiss.json',
             'data/venn10_148.json', 'data/venn11_296.json', 'data/venn12_592.json', 'data/venn13_1184.json',
             'data/venn14_2368.json', 'data/venn15_4736.json']
    for p in files:
        n, faces, edges = basic(p)
        if n == 8:
            describe_auts(n, faces, edges)
        if n == 9:
            show_meetings(n, faces)
        print()
    print('== doubling chain (BGMV doubling lemma: SoCG 2026 Lemma 10, arXiv:2511.09230v1 Lemma 11)')
    chain = ['data/venn8_37_halfturn_a.json', 'data/venn9_74.json', 'data/venn10_148.json', 'data/venn11_296.json',
             'data/venn12_592.json', 'data/venn13_1184.json', 'data/venn14_2368.json', 'data/venn15_4736.json']
    for a, b in zip(chain, chain[1:]):
        ok, why = is_doubling(a, b)
        print(f'  {b} is the doubling of {a}: {ok} ({why})')
    print()
    print('== crossings: these files (number of faces of each file) against BGMV Table 1 (Theorem 2: 40 * 2^m) and '
          'the lower bound L_n')
    bgmv = {8: 40, 9: 80, 10: 160, 11: 320, 12: 640, 13: 1280, 14: 2560, 15: 5120}
    for p in chain:
        n, faces = load(p)
        Ln = -(-((1 << n) - 2) // (n - 1))
        print(f'  n={n:2d}  L_n={Ln:5d}  BGMV={bgmv[n]:5d}  here={len(faces):5d}  (37 * 2^(n-8) = {37 << (n - 8)}; '
              f'{p})')


if __name__ == '__main__':
    main()
