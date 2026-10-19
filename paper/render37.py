#!/usr/bin/env python3
"""Draw the 37-crossing 8-Venn diagram from its dual certificate with its half-turn symmetry shown exactly.

Structure used (checked by assertions, not assumed):
  * g(x) = sigma(x) XOR 247, sigma = (0 6)(1 5)(2 4), is an orientation-preserving automorphism of the dual H.
    It fixes one face C (a crossing point) and one edge, which is an arc of curve 7 (the "line curve" L).
  * Curve L passes through all 37 crossing points, and on each side of L the regions form a tree (127 arcs).
    So the diagram is a straight line with 37 points on it and two arc diagrams of 127 non-crossing arcs, one
    above and one below.

Layout:
  1. L is the x-axis. C sits at the origin; walking along L from C the points get x = 1, 2, ..., 18 and the other
     way -1, ..., -18; the fixed arc of L runs from x = 18 through the point at infinity to x = -18.  So the two
     poles of the half-turn are the origin (the fixed crossing) and infinity (the middle of the fixed arc), and g
     is the rotation z -> -z.  Only the upper arcs are constructed; the lower ones are their exact rotations.
  2. Seed (planar by construction): each upper arc is a bracket -- a short fan segment out of its point, a vertical
     leg, and a horizontal top at its nesting rank -- with the legs at each point evenly spaced in rotation order;
     then y is scaled by sqrt(RW^2 - x^2), a homeomorphism that puts the seed in a disc.
  3. Relaxation of the upper arcs as elastic curves (tension, bending stiffness, repulsion between arcs and from the
     line, a pressure that only inflates very small regions, a barrier that keeps a minimum gap -- an angular gap
     near the points, so the fans stay open -- and an outward push on the outermost arc against a circular wall).
     Every step is planarity-preserving: each vertex, and each endpoint of a segment near it, moves less than
     0.3 x their exact vertex-to-segment distance, so no two segments can pass through each other.  Resampling is
     checked exactly and rolled back arc by arc if it would create a contact.  A final polish phase adds Taubin
     smoothing (alternating shrink / inflate Laplacian steps) and a little extra tension under the same caps, then
     3 rounds of Chaikin subdivision, also checked exactly.
  4. Verification from the drawn geometry (the script exits non-zero on failure):
     - exact segment test over all drawn polylines: contacts only at the 37 crossing points, between arcs that
       end there; each curve assembles to one simple closed curve (L closes through infinity);
     - raster read-back: even-odd scanline fill of each drawn curve gives every pixel its inside mask; all 256
       masks must occur, each as one connected component; and sampling both sides of every drawn arc must give
       the two regions the certificate says it separates (up to one global XOR, the curves whose certificate
       inside is the unbounded side);
     - the cyclic order of regions around every drawn point must equal the certificate's face cycle.

Usage: uv run --with numpy --with matplotlib --with scipy python render37.py [cert.json] [out.png] [--closed] [--pdf]
  --closed: close curve 7 with a large arc over the top instead of through infinity, so all eight curves are
  bounded (the half-turn is then exact everywhere except on that closing arc).  A picture with every curve bounded
  cannot be exactly symmetric: a rotation of the plane fixes the unbounded region, and g fixes no region.
  --pdf: also write a vector PDF next to the PNG (strokes as vectors, region colours as an embedded image).
  Environment: RX_<name> overrides a relaxation parameter (see RX below); RELAX_CACHE=<file.npz> caches the main
  relaxation (about 10 minutes); every check reruns on the final geometry either way.
"""
import json, math, os, sys
from collections import defaultdict, Counter
import numpy as np

ARGS = [a for a in sys.argv[1:] if not a.startswith('--')]
CERT = ARGS[0] if ARGS else 'data/venn8_37_halfturn_a.json'      # defaults: run from the repository root
OUT = ARGS[1] if len(ARGS) > 1 else 'build/venn8_37.png'
os.makedirs(os.path.dirname(OUT) or '.', exist_ok=True)
CLOSED = '--closed' in sys.argv

d = json.load(open(CERT))
n = d['n']; N = 1 << n
faces = [f['vertices'] for f in d['faces']]; F = len(faces)
dart = {}
for fi, f in enumerate(faces):
    for j, v in enumerate(f):
        dart[(v, f[(j + 1) % len(f)])] = fi
ARCS = {(a, b): (P, dart[(b, a)]) for (a, b), P in dart.items() if a < b}   # region pair -> its two points
E = len(ARCS)
bit = lambda a, b: (a ^ b).bit_length() - 1
assert sorted(ARCS) == sorted(tuple(sorted(e[:2])) for e in d['edges']), 'edge list disagrees with faces'

# ------------------------------------------------------------------ 0. the half-turn and the line curve
SIGMA, XMASK = [6, 5, 4, 3, 2, 1, 0, 7], 247
def g(x):
    y = 0
    for b in range(n):
        if x >> b & 1:
            y |= 1 << SIGMA[b]
    return y ^ XMASK

def canon(cyc):
    k = cyc.index(min(cyc)); return tuple(cyc[k:] + cyc[:k])
face_of = {canon(f): fi for fi, f in enumerate(faces)}
gface = {fi: face_of[canon([g(x) for x in f])] for fi, f in enumerate(faces)}   # same orientation: a rotation
assert all(tuple(sorted((g(a), g(b)))) in ARCS for a, b in ARCS), 'g is not an automorphism of H'
fixed_faces = [fi for fi in range(F) if gface[fi] == fi]
fixed_edges = [e for e in ARCS if tuple(sorted((g(e[0]), g(e[1])))) == e]
assert len(fixed_faces) == 1 and len(fixed_edges) == 1, (fixed_faces, fixed_edges)
C = fixed_faces[0]; FIXED = fixed_edges[0]; LINE = bit(*FIXED)
line_arcs = [e for e in ARCS if bit(*e) == LINE]
assert len(line_arcs) == F, 'the line curve must pass through every crossing point'
# walk the line curve from C; the fixed arc must be the one opposite C
nbr7 = defaultdict(list)
for e in line_arcs:
    P, Q = ARCS[e]; nbr7[P].append((Q, e)); nbr7[Q].append((P, e))
seq, used, cur = [C], set(), C
while True:
    nxt, e = next(x for x in nbr7[cur] if x[1] not in used)
    used.add(e)
    if nxt == C:
        break
    seq.append(nxt); cur = nxt
assert len(seq) == F and F % 2 == 1
HALF = F // 2
assert {ARCS[FIXED][0], ARCS[FIXED][1]} == {seq[HALF], seq[HALF + 1]}, 'fixed arc not opposite the fixed point'

UPBIT = 1      # regions with the line bit set are drawn above the line


def build(mirror):
    """Positions of the points on the line, and the upper arc tree."""
    X = {p: float(i if i <= HALF else i - F) for i, p in enumerate(seq)}
    if mirror:
        X = {p: -x for p, x in X.items()}
    assert all(X[gface[p]] == -X[p] for p in X)
    up = [e for e in ARCS if bit(*e) != LINE and (e[0] >> LINE & 1) == UPBIT]
    root = FIXED[0] if (FIXED[0] >> LINE & 1) == UPBIT else FIXED[1]
    rn = defaultdict(list)
    for e in up:
        rn[e[0]].append(e); rn[e[1]].append(e)
    par_arc = {root: None}; child_region = {}; order = [root]; st = [root]
    while st:
        r = st.pop()
        for e in rn[r]:
            s = e[0] if e[1] == r else e[1]
            if s not in par_arc:
                par_arc[s] = e; child_region[e] = s; st.append(s); order.append(s)
    assert len(par_arc) == N // 2 and len(child_region) == len(up) == N // 2 - 1, 'side is not a tree'
    parent = {e: par_arc[e[0] if child_region[e] == e[1] else e[1]] for e in up}
    children = defaultdict(list)
    for e, p in parent.items():
        if p is not None:
            children[p].append(e)
    iv = {e: tuple(sorted((X[ARCS[e][0]], X[ARCS[e][1]]))) for e in up}
    return X, up, parent, children, iv


DMAX = 0.42        # legs of the arcs at a point use x offsets within +-DMAX of it (points are 1 apart)


def layout(mirror):
    """Bracket seed, planar by construction.  Arc e is drawn as: a fan segment from its point up to height Y1 at
    x offset delta, a vertical leg, a horizontal top at height = its nesting rank (1 + max rank of the arcs directly
    beneath it), and the mirror image at the other end.  At a point, arcs arriving from the left get offsets in
    (-DMAX, 0) (innermost farthest out) and arcs leaving to the right offsets in (0, DMAX) (outermost nearest), so legs at one
    point are ordered, legs of different points are disjoint, and nested arcs have nested legs and higher tops.
    Then y is scaled by sqrt(RW^2 - x^2) / (H + 1), a homeomorphism of the strip |x| < RW that puts the seed inside
    the disc of radius RW."""
    X, up, parent, children, iv = build(mirror)
    rank = {}
    def rk(e):
        if e not in rank:
            rank[e] = 1 + max((rk(c) for c in children[e]), default=0)
        return rank[e]
    for e in up:
        rk(e)
    H = max(rank.values())
    for e in up:
        for c in children[e]:
            assert rank[c] < rank[e]
    off = {}
    for p, xp in X.items():
        left = sorted([e for e in up if p in ARCS[e] and iv[e][1] == xp], key=lambda e: rank[e])          # inner first
        right = sorted([e for e in up if p in ARCS[e] and iv[e][0] == xp], key=lambda e: -rank[e])       # outer first
        for k, e in enumerate(left):      # arcs arriving from the left lean left, innermost farthest out
            off[(e, p)] = -DMAX + (k + 0.5) * DMAX / len(left)
        for k, e in enumerate(right):     # arcs leaving to the right lean right, outermost nearest the point
            off[(e, p)] = (k + 0.5) * DMAX / len(right)
    RW = max(abs(x) for x in X.values()) + 2.5
    Y1 = 0.5
    geo = {}
    for e in up:
        pa, pb = sorted(ARCS[e], key=lambda p: X[p])
        xa, xb = X[pa], X[pb]
        da, db = off[(e, pa)], off[(e, pb)]
        Y = float(rank[e])
        top = np.linspace(xa + da, xb + db, max(3, int((xb + db - xa - da) / 0.02)))
        pts = np.concatenate([[[xa, 0], [xa + da, Y1]], np.stack([top, np.full(len(top), Y)], 1),
                              [[xb + db, Y1], [xb, 0]]]).astype(float)
        pts[:, 1] *= np.sqrt(RW ** 2 - pts[:, 0] ** 2) / (H + 1)     # the top is densely sampled, so it follows the map
        geo[e] = pts
    return X, up, parent, children, iv, rank, geo


def first_angles(X, up, geo):
    alpha = {}
    for e in up:
        P_ = geo[e]
        for p in ARCS[e]:
            Q_ = P_ if abs(P_[0, 0] - X[p]) < 1e-12 and abs(P_[0, 1]) < 1e-12 else P_[::-1]
            v = Q_[1] - Q_[0]
            alpha[(e, p)] = math.atan2(v[1], v[0])
    return alpha


def drawn_rotation(X, up, alpha):
    """Cyclic region order around each point in the drawing (counter-clockwise)."""
    rot = {}
    for p in X:
        items = []
        for e in up:
            if (e, p) in alpha:
                items.append((alpha[(e, p)], e))
        gp = gface[p]
        for e in up:
            if (e, gp) in alpha:   # lower arc g(e) at p, the rotation of upper arc e at g(p)
                items.append((alpha[(e, gp)] + math.pi, tuple(sorted((g(e[0]), g(e[1]))))))
        for e in line_arcs:
            P, Q = ARCS[e]
            if p in (P, Q):
                q = Q if P == p else P
                if FIXED == e:
                    items.append((0.0 if X[p] > 0 else math.pi, e))
                else:
                    items.append((0.0 if X[q] > X[p] else math.pi, e))
        items.sort()
        regs = []
        for (a1, e1), (a2, e2) in zip(items, items[1:] + items[:1]):
            common = set(e1) & set(e2)
            assert len(common) == 1, ('consecutive arcs share no region', p, e1, e2)
            regs.append(common.pop())
        rot[p] = regs
    return rot


def same_cycle(r, f):
    if len(r) != len(f):
        return False
    k = f.index(r[0])
    return f[k:] + f[:k] == r


# build; mirror if the drawing comes out clockwise relative to the certificate's face cycles
for MIRROR in (False, True):
    X, up, parent, children, iv, rank, geo = layout(MIRROR)
    alpha = first_angles(X, up, geo)
    rot = drawn_rotation(X, up, alpha)
    ccw = sum(same_cycle(rot[p], faces[p]) for p in X)
    cw = sum(same_cycle(rot[p][::-1], faces[p]) for p in X)
    if ccw == F:
        break
    assert cw == F, f'drawn rotation matches neither orientation ({ccw}, {cw})'
print(f'seed layout: line curve {LINE}, fixed crossing {C} at the origin, fixed arc {FIXED} through infinity; '
      f'{len(up)} upper arcs, nesting rank up to {max(rank.values())}; rotation = certificate face cycles at all '
      f'{F} points (mirror={MIRROR})', flush=True)
XM = max(abs(x) for x in X.values())

# ------------------------------------------------------------------ 3b. planarity-preserving relaxation
# The seed is planar but crude (brackets).  The upper arcs are relaxed as elastic curves: weak tension, bending
# stiffness, repulsion between different arcs (and from the line), a pressure that only inflates regions smaller
# than AMIN, a barrier that keeps a minimum gap (an angular gap near the points, so the fans stay open), and an
# outward push on the outermost arc against a circular wall.  In every step each vertex, and each endpoint of a
# segment near it, moves less than CAPF = 0.3 x their exact vertex-to-segment distance; segment distance is
# 1-Lipschitz in the endpoints, so no two segments can pass through each other.  Resampling (every 25 steps) is
# checked exactly and undone arc by arc if it would create a contact.  The lower arcs are the exact 180-degree
# rotations of the result.
from scipy.spatial import cKDTree
RX = dict(S=0.12, SMIN=0.004, DBAR=0.05, KBAR=10.0, ITERS=2000, ETA=0.05, KT=0.2, KB=0.3, KR=0.02, RC=1.2, MU=0.5,
          KP=1.0, AMIN=1.5, FILT=3, KO=0.4, KW=3.0, RWALL=XM + 2.5, CAPF=0.3, POLISH=1000, TAUL=0.5, TAUM=-0.53,
          KTP=0.3, SMOOTH=600, KTS=0.2)
for k_ in list(RX):
    if os.environ.get('RX_' + k_):
        RX[k_] = type(RX[k_])(os.environ['RX_' + k_])


def resample_var(pts, S=RX['S'], smin=RX['SMIN']):
    """Resample a polyline with spacing min(S, 0.45 r), r = arclength to the nearer end (dense near points)."""
    seg = np.linalg.norm(np.diff(pts, axis=0), axis=1)
    keep = np.r_[True, seg > 0]; pts = pts[keep]
    seg = np.linalg.norm(np.diff(pts, axis=0), axis=1)
    cs = np.concatenate([[0], np.cumsum(seg)]); L = cs[-1]
    fine = np.linspace(0, L, max(200, int(L / (smin / 2))))
    r = np.minimum(fine, L - fine)
    dens = 1 / np.clip(0.45 * r, smin, S)
    u = np.concatenate([[0], np.cumsum(0.5 * (dens[1:] + dens[:-1]) * np.diff(fine))])
    k = max(int(math.ceil(u[-1])), 6)
    q = np.interp(np.linspace(0, u[-1], k + 1), u, fine)
    out = np.stack([np.interp(q, cs, pts[:, 0]), np.interp(q, cs, pts[:, 1])], 1)
    out[0] = pts[0]; out[-1] = pts[-1]
    return out


POINT_SET = {(float(x), 0.0) for x in X.values()}


def conflicts(polys):
    """Arc index pairs whose polylines touch or cross anywhere except at a shared crossing point."""
    S_ = np.concatenate([np.stack([P[:-1], P[1:]], 1) for P in polys])
    own = np.concatenate([np.full(len(P) - 1, k) for k, P in enumerate(polys)])
    idx = np.concatenate([np.arange(len(P) - 1) for P in polys])
    lo = S_.min(1); hi = S_.max(1); h = 0.05
    gx0 = np.floor(lo[:, 0] / h).astype(np.int64); gx1 = np.floor(hi[:, 0] / h).astype(np.int64)
    gy0 = np.floor(lo[:, 1] / h).astype(np.int64); gy1 = np.floor(hi[:, 1] / h).astype(np.int64)
    cells, sid = [], []
    for dx in range(int((gx1 - gx0).max()) + 1):
        for dy in range(int((gy1 - gy0).max()) + 1):
            ok = (gx0 + dx <= gx1) & (gy0 + dy <= gy1)
            cells.append((gx0[ok] + dx) * 1000003 + gy0[ok] + dy); sid.append(np.nonzero(ok)[0])
    cells = np.concatenate(cells); sid = np.concatenate(sid)
    o = np.lexsort((sid, cells)); cells = cells[o]; sid = sid[o]
    st_ = np.r_[0, np.nonzero(np.diff(cells))[0] + 1]; cnt = np.diff(np.r_[st_, len(cells)])
    I, J = [], []
    for k in range(1, int(cnt.max())):
        sel = cnt > k; base = st_[sel]; c = cnt[sel]
        for off in range(0, int(c.max()) - k):
            ok = off + k < c
            I.append(sid[base[ok] + off]); J.append(sid[base[ok] + off + k])
    if not I:
        return set()
    I = np.concatenate(I); J = np.concatenate(J)
    pr_ = np.unique(np.minimum(I, J) * len(S_) + np.maximum(I, J)); I = pr_ // len(S_); J = pr_ % len(S_)
    keep = ~((own[I] == own[J]) & (np.abs(idx[I] - idx[J]) <= 1)); I, J = I[keep], J[keep]
    A0, A1, B0, B1 = S_[I, 0], S_[I, 1], S_[J, 0], S_[J, 1]
    box = ((np.maximum(A0, A1) >= np.minimum(B0, B1)) & (np.maximum(B0, B1) >= np.minimum(A0, A1))).all(1)
    I, J, A0, A1, B0, B1 = I[box], J[box], A0[box], A1[box], B0[box], B1[box]
    orient = lambda p, q, r: (q[:, 0] - p[:, 0]) * (r[:, 1] - p[:, 1]) - (q[:, 1] - p[:, 1]) * (r[:, 0] - p[:, 0])
    o1, o2, o3, o4 = orient(A0, A1, B0), orient(A0, A1, B1), orient(B0, B1, A0), orient(B0, B1, A1)
    hit = (o1 * o2 <= 0) & (o3 * o4 <= 0)
    out = set()
    for t in np.nonzero(hit)[0]:
        sh = [p for p in (A0[t], A1[t]) if any(np.array_equal(p, q) for q in (B0[t], B1[t]))]
        if sh and (float(sh[0][0]), float(sh[0][1])) in POINT_SET and not ((o1[t] * o2[t] < 0) and (o3[t] * o4[t] < 0)):
            continue
        if not sh and A0[t, 1] == A1[t, 1] == B0[t, 1] == B1[t, 1] == 0:      # collinear pieces of the line
            continue
        out.add((int(own[I[t]]), int(own[J[t]])))
    return out


def add_at(n_, idx, vec):
    """Sum of 2-vectors vec into n_ slots by index (np.add.at, but fast)."""
    return np.stack([np.bincount(idx, weights=vec[:, 0], minlength=n_),
                     np.bincount(idx, weights=vec[:, 1], minlength=n_)], 1)


def min_at(arr, idx, vals):
    """arr[idx] = minimum(arr[idx], vals) with repeated indices (np.minimum.at, but fast)."""
    np.minimum.at(arr, idx, vals)


def relax(upper_polys, outer_k, iters, polish=False, smooth=False):
    aid = {e: k for k, e in enumerate(up)}
    par_idx = np.array([aid[parent[e]] if parent[e] is not None else -1 for e in up])
    ch_lists = [[aid[c] for c in children[e]] for e in up]
    XS = sorted(set(X.values()))
    ext = [XS[0] - 2.0] + XS + [XS[-1] + 2.0]
    lx = np.concatenate([np.linspace(a, b, int(round((b - a) / (RX['S'] * 0.5))) + 1)[:-1]
                         for a, b in zip(ext[:-1], ext[1:])] + [[ext[-1]]])
    line = np.stack([lx, np.zeros(len(lx))], 1)
    nl = len(line)

    def pack(polys):
        V = np.concatenate(polys)
        arc_of = np.concatenate([np.full(len(p), k) for k, p in enumerate(polys)])
        start = np.cumsum([0] + [len(p) for p in polys])
        fixed = np.zeros(len(V), bool); fixed[start[:-1]] = True; fixed[start[1:] - 1] = True
        return V, arc_of, start, fixed

    def seg_point_dist(p, a, b):
        ab = b - a; t = np.clip(((p - a) * ab).sum(1) / np.maximum((ab * ab).sum(1), 1e-30), 0, 1)
        return np.linalg.norm(p - (a + t[:, None] * ab), axis=1)

    polys = [resample_var(P) for P in upper_polys]
    level = [0] * len(polys)
    while True:      # arcs whose coarse resampling would touch a neighbour start from a finer resampling
        bad = conflicts(polys + [line])
        ks = {k for pair in bad for k in pair if k < len(polys)}
        if not bad:
            break
        todo = [k for k in ks if level[k] < 4]
        assert todo, ('initial layout is not planar', bad)
        for k in todo:
            level[k] += 1
            polys[k] = resample_var(upper_polys[k], S=RX['S'] / 2 ** level[k], smin=RX['SMIN'] / 2 ** level[k])
    print(f'  relax start: {sum(len(p) for p in polys)} vertices, {sum(l > 0 for l in level)} arcs '
          f'resampled finer at first', flush=True)
    V, arc_of, start, fixed = pack(polys)
    for it in range(iters):
        n_ = len(V)
        is_last = np.zeros(n_, bool); is_last[start[1:] - 1] = True
        is_first = np.zeros(n_, bool); is_first[start[:-1]] = True
        sa = np.nonzero(~is_last)[0]; sb = sa + 1
        dv = V[sb] - V[sa]; L = np.linalg.norm(dv, axis=1); T = dv / L[:, None]
        seg_id = np.full(n_, -1); seg_id[sa] = np.arange(len(sa))
        tr = (V[sb, 0] - V[sa, 0]) * (V[sa, 1] + V[sb, 1]) / 2
        Aarc = np.bincount(arc_of[sa], weights=tr, minlength=len(up))
        Areg = Aarc - np.array([sum(Aarc[c] for c in cl) for cl in ch_lists])
        press = RX['KP'] * np.maximum(0, np.log(RX['AMIN'] / np.maximum(Areg, 1e-6)))
        dpress = press - np.where(par_idx >= 0, press[np.maximum(par_idx, 0)], 0.0)
        dpress[outer_k] += RX['KO']
        iv_ = np.nonzero(~fixed)[0]
        sA, sB = seg_id[iv_], seg_id[iv_ - 1]
        F = np.zeros_like(V)
        F[iv_] += RX['KT'] * (T[sA] - T[sB])
        tang = V[iv_ + 1] - V[iv_ - 1]; tn = np.linalg.norm(tang, axis=1); tu = tang / tn[:, None]
        nrm = np.stack([-tu[:, 1], tu[:, 0]], 1)
        w = np.zeros(n_); w[iv_] = 0.5 * (L[sA] + L[sB])
        Fpress = np.zeros_like(V); Fpress[iv_] = (dpress[arc_of[iv_]] * w[iv_])[:, None] * nrm
        F += Fpress
        # spacing toward the target density along the arc
        r_mid = np.zeros(len(sa))
        for k in range(len(start) - 1):
            sk = seg_id[start[k]:start[k + 1] - 1]
            c_ = np.concatenate([[0], np.cumsum(L[sk])]); m_ = 0.5 * (c_[1:] + c_[:-1])
            r_mid[sk] = np.minimum(m_, c_[-1] - m_)
        tseg = np.clip(0.45 * r_mid, RX['SMIN'], RX['S'])
        F[iv_] += RX['MU'] * (L[sA] / tseg[sA] - L[sB] / tseg[sB])[:, None] * \
            (0.5 * (tseg[sA] + tseg[sB]))[:, None] * tu
        lap = np.zeros_like(V); lap[iv_] = V[iv_ - 1] + V[iv_ + 1] - 2 * V[iv_]
        bl = np.zeros_like(V); bl[iv_] = lap[iv_ - 1] + lap[iv_ + 1] - 2 * lap[iv_]
        F -= RX['KB'] * bl / RX['S']
        # repulsion (line density weighted) between different arcs and from the line
        allp = np.concatenate([V, line]); allarc = np.concatenate([arc_of, np.full(nl, -1)])
        wall = np.concatenate([w, np.full(nl, RX['S'] * 0.5)])
        maxseg = float(L.max())
        rcap = max(0.6, 2 * maxseg + 0.25)
        pr = cKDTree(allp).query_pairs(max(RX['RC'], rcap), output_type='ndarray')
        i0, j0 = pr[:, 0], pr[:, 1]
        dd0 = allp[i0] - allp[j0]; dist0 = np.linalg.norm(dd0, axis=1)
        selfpair = (allarc[i0] == allarc[j0]) & (allarc[i0] >= 0)     # segments containing the vertex are skipped below
        capsel = ((allarc[i0] != allarc[j0]) | selfpair) & (dist0 < rcap)
        o_ = (allarc[i0] != allarc[j0]) & (dist0 > 1e-12) & (dist0 < RX['RC'])
        i, j, dd, dist = i0[o_], j0[o_], dd0[o_], dist0[o_]
        mag = RX['KR'] * (RX['RC'] / dist - 1)
        u_ = dd / dist[:, None]
        Fall = add_at(len(allp), i, (mag * wall[j])[:, None] * u_) - add_at(len(allp), j, (mag * wall[i])[:, None] * u_)
        F += Fall[:n_]
        # exact vertex-to-foreign-segment distances (other arcs, the line, far parts of the same arc)
        ic, jc = i0[capsel], j0[capsel]
        PS, AS, TS, VS = [], [], [], []
        # each segment (q, q+1) whose distance to p is below rcap - maxseg has q within rcap of p, so taking the
        # segment that starts at the partner vertex finds every relevant (vertex, segment) pair exactly once
        for p_, q_ in ((ic, jc), (jc, ic)):
            ok = np.where(q_ < n_, ~is_last[np.minimum(q_, n_ - 1)], q_ < len(allp) - 1)
            a_ = np.where(ok, q_, 0); b_ = a_ + 1
            ok &= (p_ != a_) & (p_ != b_)
            ok &= ~((np.abs(allp[p_] - allp[a_]).sum(1) == 0) | (np.abs(allp[p_] - allp[b_]).sum(1) == 0))
            PS.append(p_[ok]); AS.append(a_[ok])
        PS = np.concatenate(PS); AS = np.concatenate(AS); BS = AS + 1
        ab = allp[BS] - allp[AS]
        TS = np.clip(((allp[PS] - allp[AS]) * ab).sum(1) / np.maximum((ab * ab).sum(1), 1e-30), 0, 1)
        VS = allp[PS] - (allp[AS] + TS[:, None] * ab)
        DS = np.maximum(np.linalg.norm(VS, axis=1), 1e-300)
        # barrier: keep at least dbar from foreign geometry; near a point dbar shrinks with the distance r to the
        # point (an angular gap of about 0.2 rad), so the fans stay open
        r_end = np.minimum(np.linalg.norm(V - V[start[:-1]][arc_of], axis=1),
                           np.linalg.norm(V - V[start[1:] - 1][arc_of], axis=1))
        dbar = np.concatenate([np.minimum(RX['DBAR'], 0.2 * r_end), np.full(nl, RX['DBAR'])])
        thr = np.minimum(dbar[PS], (1 - TS) * dbar[AS] + TS * dbar[BS])     # dbar at the closest point
        # inside one arc only a weak barrier (a strong one would hold folds open; none lets a fold close up)
        same_arc = allarc[PS] == allarc[AS]
        thr = np.where(same_arc, 0.3 * thr, thr)
        hb = (~same_arc | ((np.abs(PS - AS) >= 3) & (np.abs(PS - BS) >= 3))) & (DS < thr)
        fb = (RX['KBAR'] * ((thr[hb] / DS[hb]) ** 2 - 1))[:, None] * VS[hb] / DS[hb][:, None]
        Fb = (add_at(len(allp), PS[hb], fb) - add_at(len(allp), AS[hb], (1 - TS[hb])[:, None] * fb)
              - add_at(len(allp), BS[hb], TS[hb][:, None] * fb))
        F += Fb[:n_]
        Fpol = Fb[:n_] + Fpress      # what the final smoothing stage keeps: barrier, wall, small-region pressure
        # soft circular wall
        rad = np.linalg.norm(V, axis=1); over = (rad > RX['RWALL'] - 0.3) & (arc_of == outer_k) & ~fixed
        fw = (RX['KW'] * (rad[over] - (RX['RWALL'] - 0.3)))[:, None] * V[over] / rad[over][:, None]
        F[over] -= fw; Fpol[over] -= fw
        F[fixed] = 0
        for _ in range(RX['FILT']):
            G = F.copy(); G[iv_] = 0.25 * F[iv_ - 1] + 0.5 * F[iv_] + 0.25 * F[iv_ + 1]; F = G; F[fixed] = 0
        # planarity caps: a vertex and the endpoints of a segment near it each move < CAPF x their distance
        cap = np.full(len(allp), RX['CAPF'] * (rcap - maxseg))
        min_at(cap, PS, RX['CAPF'] * DS); min_at(cap, AS, RX['CAPF'] * DS); min_at(cap, BS, RX['CAPF'] * DS)
        if smooth:     # last stage: Taubin smoothing with only barrier, wall, small-region pressure, mild tension
            Fpol[iv_] += RX['KTS'] * (T[sA] - T[sB])
            D = RX['ETA'] * Fpol + (RX['TAUL'] if it % 2 == 0 else RX['TAUM']) * 0.5 * lap
            D[fixed] = 0
        elif polish:   # Taubin smoothing (alternating shrink / inflate Laplacian steps) on top of the forces
            F[iv_] += RX['KTP'] * (T[sA] - T[sB])     # all relaxation forces, a little extra tension,
            D = RX['ETA'] * F + (RX['TAUL'] if it % 2 == 0 else RX['TAUM']) * 0.5 * lap     # and Taubin
            D[fixed] = 0
        else:
            D = RX['ETA'] * F
        m_ = np.linalg.norm(D, axis=1)
        Vold = V
        V = V + D * np.minimum(1, cap[:n_] / np.maximum(m_, 1e-30))[:, None]
        if os.environ.get('RX_DEBUG'):
            lost = conflicts([V[start[k]:start[k + 1]] for k in range(len(start) - 1)] + [line])
            if lost:
                print('lost at step', it, sorted(lost)[:5], 'maxseg', maxseg, 'rcap', rcap)
                k1, k2 = sorted(lost)[0]
                for k in (k1, k2):
                    if k < len(start) - 1:
                        P0 = Vold[start[k]:start[k + 1]]; P1 = V[start[k]:start[k + 1]]
                        mv = np.linalg.norm(P1 - P0, axis=1)
                        print(' arc', k, 'len', len(P0), 'max move', mv.max(), 'at', np.argmax(mv), P0[np.argmax(mv)],
                              'cap there', cap[start[k] + np.argmax(mv)])
                np.savez(os.environ['RX_DEBUG'],
                         Vold=Vold, V=V, start=start, k1=k1, k2=k2, cap=cap[:n_], line=line)
                raise SystemExit('debug stop')
        if it % 25 == 24 or it == iters - 1:
            old = [V[start[k]:start[k + 1]].copy() for k in range(len(start) - 1)]
            lost = conflicts(old + [line])
            assert not lost, ('relaxation step lost planarity', it, lost)
            new = [resample_var(P) for P in old]
            lev = [0] * len(old); redo = set()
            while True:     # an arc whose resampling would touch something is resampled finer, else kept as is
                bad = conflicts(new + [line])
                ks = {k for pair in bad for k in pair if k < len(old)}
                if not bad:
                    break
                todo = [k for k in ks if lev[k] < 3]
                assert todo or ks <= redo, bad
                if not todo:
                    break
                for k in todo:
                    lev[k] += 1
                    if lev[k] < 3:
                        new[k] = resample_var(old[k], S=RX['S'] / 2 ** lev[k], smin=RX['SMIN'])
                    else:
                        new[k] = old[k]; redo.add(k)
            assert not conflicts(new + [line])
            if it % 200 == 199 or it == iters - 1:
                print(f'  {"smooth" if smooth else "polish" if polish else "relax"} {it + 1}/{iters}: region area min {Areg.min():.3f} median '
                      f'{np.median(Areg):.3f}; longest segment {maxseg:.3f}; resample kept old polylines for '
                      f'{len(redo)} arcs', flush=True)
            V, arc_of, start, fixed = pack(new)
    return [V[start[k]:start[k + 1]].copy() for k in range(len(start) - 1)]


def chaikin(P, rounds=3):
    for _ in range(rounds):
        q = 0.75 * P[:-1] + 0.25 * P[1:]; r = 0.25 * P[:-1] + 0.75 * P[1:]
        mid = np.empty((2 * (len(P) - 1), 2)); mid[0::2] = q; mid[1::2] = r
        P = np.vstack([P[:1], mid[1:-1], P[-1:]])
    return P


outer_k = up.index(next(e for e in up if parent[e] is None))
if RX['ITERS'] > 0:
    # optional cache of the relaxed upper arcs (it is only an input to the checks below, which always rerun)
    CACHE = os.environ.get('RELAX_CACHE')
    if CACHE and os.path.exists(CACHE):
        zc = np.load(CACHE)
        relaxed = [zc[f'a{k}'] for k in range(len(up))]
        print('relaxed arcs loaded from', CACHE)
    else:
        relaxed = relax([geo[e] for e in up], outer_k, RX['ITERS'])
        if CACHE:
            np.savez(CACHE, **{f'a{k}': P_ for k, P_ in enumerate(relaxed)})
    for k, e in enumerate(up):      # endpoints must be exactly the points
        assert relaxed[k][0, 1] == 0 and relaxed[k][-1, 1] == 0 and {relaxed[k][0, 0], relaxed[k][-1, 0]} == set(iv[e])
    PCACHE = os.environ.get('POLISH_CACHE')
    if PCACHE and os.path.exists(PCACHE):
        zc = np.load(PCACHE)
        relaxed = [zc[f'a{k}'] for k in range(len(up))]
        print('polished arcs loaded from', PCACHE)
    elif RX['POLISH'] > 0:
        relaxed = relax(relaxed, outer_k, RX['POLISH'], polish=True)
        if PCACHE:
            np.savez(PCACHE, **{f'a{k}': P_ for k, P_ in enumerate(relaxed)})
    if RX['SMOOTH'] > 0:
        relaxed = relax(relaxed, outer_k, RX['SMOOTH'], smooth=True)
    smooth = [chaikin(P) for P in relaxed]
    XS_ = sorted(set(X.values()))
    line_poly = np.stack([np.array([XS_[0] - 2.0] + XS_ + [XS_[-1] + 2.0]), np.zeros(len(XS_) + 2)], 1)
    bad = conflicts(smooth + [line_poly])
    if bad:      # fall back to the unsmoothed polyline for any arc whose smoothing created a contact
        ks = {k for pair in bad for k in pair if k < len(smooth)}
        smooth = [relaxed[k] if k in ks else smooth[k] for k in range(len(smooth))]
        assert not conflicts(smooth + [line_poly])
    for k, e in enumerate(up):
        geo[e] = smooth[k]
    alpha = first_angles(X, up, geo)
    rot = drawn_rotation(X, up, alpha)
    assert all(same_cycle(rot[p], faces[p]) for p in X), 'relaxed drawing changed the rotation at a point'
    print(f'relaxed: rotation at all {F} points still equals the certificate face cycles', flush=True)

# ------------------------------------------------------------------ lower arcs, line, curves
PT = {p: np.array([X[p], 0.0]) for p in X}
arc_xy = {}     # region pair -> polyline (from its point with smaller x to larger x for upper arcs)
for e in up:
    arc_xy[e] = geo[e]
    ge = tuple(sorted((g(e[0]), g(e[1]))))
    arc_xy[ge] = -geo[e]
assert len(arc_xy) == E - F
XM = max(abs(x) for x in X.values())
RMAX = max(float(np.linalg.norm(P_, axis=1).max()) for P_ in arc_xy.values())   # extent of the drawn arcs
R_LINE = RMAX + 1.6                  # how far the line is drawn before it leaves the picture
R_CLOSE = RMAX + 0.5                 # radius of the closing arc of the line curve (--closed)
for e in line_arcs:
    P, Q = ARCS[e]
    if e == FIXED:
        continue
    a, b = sorted((X[P], X[Q]))
    arc_xy[e] = np.stack([np.linspace(a, b, 3), np.zeros(3)], 1)
Pm, Qm = ARCS[FIXED]
left_end, right_end = (Pm, Qm) if X[Pm] < X[Qm] else (Qm, Pm)
if CLOSED:
    # along the line to a small fillet (radius RHO, tangent to the line and to the big circle), over the top, back
    RHO = 0.35
    cx = math.sqrt((R_CLOSE - RHO) ** 2 - RHO ** 2); a0 = math.atan2(RHO, cx)
    tf = np.linspace(-np.pi / 2, a0, 200)
    fil = np.stack([cx + RHO * np.cos(tf), RHO + RHO * np.sin(tf)], 1)          # right fillet, bottom to top
    th = np.linspace(a0, np.pi - a0, 4000)
    big = np.stack([R_CLOSE * np.cos(th), R_CLOSE * np.sin(th)], 1)
    closing = np.concatenate([[[XM, 0.0]], fil, big[1:-1], (fil * [-1, 1])[::-1], [[-XM, 0.0]]])
    arc_xy[FIXED] = closing                                  # from right_end over the top to left_end
    FIXED_PIECES = [closing]
else:
    FIXED_PIECES = [np.array([[XM, 0.0], [R_LINE, 0.0]]), np.array([[-R_LINE, 0.0], [-XM, 0.0]])]
ends = {e: (ARCS[e][0], ARCS[e][1]) for e in ARCS}
for e, P in arc_xy.items():                                  # pin endpoints to the exact point coordinates
    p, q = ends[e]
    if np.linalg.norm(P[0] - PT[p]) > np.linalg.norm(P[0] - PT[q]):
        p, q = q, p
    assert np.linalg.norm(P[0] - PT[p]) < 1e-9 and np.linalg.norm(P[-1] - PT[q]) < 1e-9, e
    P[0] = PT[p]; P[-1] = PT[q]

curves = []          # closed polylines for the raster fill (the line curve is closed far outside the picture)
curve_draw = []      # what is stroked
for j in range(n):
    es = [e for e in ARCS if bit(*e) == j]
    at = defaultdict(list)
    for e in es:
        at[ends[e][0]].append(e); at[ends[e][1]].append(e)
    assert all(len(v) == 2 for v in at.values()), f'curve {j} passes a point more than once'
    e0 = es[0]; p = ends[e0][0]; e = e0; seqpts = []; seen = set()
    while e not in seen:
        seen.add(e)
        q = ends[e][1] if ends[e][0] == p else ends[e][0]
        if j == LINE and e == FIXED and not CLOSED:
            seqpts.append(None)        # the arc through infinity
        else:
            pts = arc_xy[e]
            if np.linalg.norm(pts[0] - PT[p]) > 1e-9:
                pts = pts[::-1]
            seqpts.append(pts)
        p = q
        e = next(x for x in at[p] if x != e)
    assert len(seen) == len(es), f'curve {j} is not a single cycle'
    if j == LINE and not CLOSED:
        k = next(i for i, x in enumerate(seqpts) if x is None)
        chain = seqpts[k + 1:] + seqpts[:k]
        poly = np.concatenate([c[:-1] for c in chain] + [chain[-1][-1:]])
        if poly[0, 0] > poly[-1, 0]:
            poly = poly[::-1]
        draw = np.concatenate([[[-R_LINE, 0.0]], poly, [[R_LINE, 0.0]]])
        BIG = 1e3
        fillpoly = np.concatenate([[[-BIG, 0.0]], poly, [[BIG, 0.0], [BIG, BIG], [-BIG, BIG], [-BIG, 0.0]]])
        curves.append(fillpoly); curve_draw.append(draw)
    else:
        poly = np.concatenate([c[:-1] for c in seqpts])
        poly = np.vstack([poly, poly[:1]])
        curves.append(poly); curve_draw.append(poly)

# ------------------------------------------------------------------ verification 1: exact segment test
def segment_test():
    segs, own = [], []
    pieces = [(e, P) for e, P in arc_xy.items() if not (e == FIXED and not CLOSED)]
    pieces += [(FIXED, P) for P in (FIXED_PIECES if not CLOSED else [])]
    for k, (e, P) in enumerate(pieces):
        segs.append(np.stack([P[:-1], P[1:]], 1)); own.append(np.full(len(P) - 1, k))
    S = np.concatenate(segs); own = np.concatenate(own)
    idx = np.concatenate([np.arange(len(s)) for s in segs])
    lo = S.min(1); hi = S.max(1)
    h = 0.02
    gx0 = np.floor(lo[:, 0] / h).astype(np.int64); gx1 = np.floor(hi[:, 0] / h).astype(np.int64)
    gy0 = np.floor(lo[:, 1] / h).astype(np.int64); gy1 = np.floor(hi[:, 1] / h).astype(np.int64)
    cells, sid = [], []
    for dx in range(int((gx1 - gx0).max()) + 1):
        for dy in range(int((gy1 - gy0).max()) + 1):
            ok = (gx0 + dx <= gx1) & (gy0 + dy <= gy1)
            cx = gx0[ok] + dx; cy = gy0[ok] + dy
            cells.append(cx * 1000003 + cy); sid.append(np.nonzero(ok)[0])
    cells = np.concatenate(cells); sid = np.concatenate(sid)
    o = np.lexsort((sid, cells)); cells = cells[o]; sid = sid[o]
    start = np.r_[0, np.nonzero(np.diff(cells))[0] + 1]; cnt = np.diff(np.r_[start, len(cells)])
    I, J = [], []
    for k in range(1, int(cnt.max())):
        sel = cnt > k
        base = start[sel]; c = cnt[sel]
        for off in range(0, int(c.max()) - k):
            ok = off + k < c
            I.append(sid[base[ok] + off]); J.append(sid[base[ok] + off + k])
    I = np.concatenate(I); J = np.concatenate(J)
    a, b = np.minimum(I, J), np.maximum(I, J)
    pairs = np.unique(a * len(S) + b); I = pairs // len(S); J = pairs % len(S)
    same = own[I] == own[J]
    keep = ~(same & (np.abs(idx[I] - idx[J]) <= 1))
    I, J = I[keep], J[keep]
    A0, A1, B0, B1 = S[I, 0], S[I, 1], S[J, 0], S[J, 1]
    box = ((np.maximum(A0, A1) >= np.minimum(B0, B1)) & (np.maximum(B0, B1) >= np.minimum(A0, A1))).all(1)
    I, J, A0, A1, B0, B1 = I[box], J[box], A0[box], A1[box], B0[box], B1[box]
    orient = lambda p, q, r: (q[:, 0] - p[:, 0]) * (r[:, 1] - p[:, 1]) - (q[:, 1] - p[:, 1]) * (r[:, 0] - p[:, 0])
    o1, o2, o3, o4 = orient(A0, A1, B0), orient(A0, A1, B1), orient(B0, B1, A0), orient(B0, B1, A1)
    proper = (o1 * o2 < 0) & (o3 * o4 < 0)
    touch = ~proper & (o1 * o2 <= 0) & (o3 * o4 <= 0)
    ptarr = np.array([PT[p] for p in sorted(PT)]); pid = sorted(PT)
    bad, contacts = int(proper.sum()), set()
    for t in np.nonzero(touch)[0]:
        sh = [p for p in (A0[t], A1[t]) if any(np.array_equal(p, q) for q in (B0[t], B1[t]))]
        if not sh:
            # collinear pieces of the line curve meeting end to end are fine; anything else is not
            if abs(A0[t, 1]) + abs(A1[t, 1]) + abs(B0[t, 1]) + abs(B1[t, 1]) == 0:
                xa = sorted((A0[t, 0], A1[t, 0])); xb = sorted((B0[t, 0], B1[t, 0]))
                if xa[1] <= xb[0] or xb[1] <= xa[0]:
                    continue
            bad += 1; continue
        k = np.nonzero((ptarr == sh[0]).all(1))[0]
        ea, eb = pieces[own[I[t]]][0], pieces[own[J[t]]][0]
        if len(k) != 1 or pid[k[0]] not in ARCS[ea] or pid[k[0]] not in ARCS[eb]:
            bad += 1; continue
        if bit(*ea) != bit(*eb):
            contacts.add(pid[k[0]])
    return len(S), len(I), bad, contacts

nseg, npairs, bad, contacts = segment_test()
mult = Counter(len(faces[p]) // 2 for p in contacts)
print(f'segment test: {nseg} segments, {npairs} close pairs tested, {bad} crossings/touches away from the '
      f'crossing points; curves meet at exactly {len(contacts)} points ({dict(mult)} by number of curves through)')
SEG_OK = bad == 0 and contacts == set(range(F))
# readability: smallest distance between two different arcs (or an arc and the line) away from the points
_pts = [(P_, k) for k, (e, P_) in enumerate(arc_xy.items()) if bit(*e) != LINE]
_V = np.concatenate([P_ for P_, k in _pts]); _A = np.concatenate([np.full(len(P_), k) for P_, k in _pts])
_far = np.min(np.stack([np.hypot(_V[:, 0] - x, _V[:, 1]) for x in X.values()]), axis=0) > 0.5
_dd, _ii = cKDTree(_V).query(_V[_far], k=40)
_other = _A[_ii] != _A[_far][:, None]
_gap = np.where(_other, _dd, np.inf).min(1)
MIN_GAP = float(min(_gap.min(), np.abs(_V[_far, 1]).min()))
_rk = []
for e, P_ in arc_xy.items():
    if bit(*e) == LINE or len(P_) < 3:
        continue
    v1 = P_[1:-1] - P_[:-2]; v2 = P_[2:] - P_[1:-1]
    l1 = np.linalg.norm(v1, axis=1); l2 = np.linalg.norm(v2, axis=1)
    ang = np.abs(np.arctan2(v1[:, 0] * v2[:, 1] - v1[:, 1] * v2[:, 0], (v1 * v2).sum(1)))
    rad_ = 0.5 * (l1 + l2) / np.maximum(ang, 1e-12)
    farp = np.min(np.stack([np.hypot(P_[1:-1, 0] - x, P_[1:-1, 1]) for x in X.values()]), axis=0) > 0.3
    _rk.append(rad_[farp])
_rk = np.concatenate(_rk)
print(f'curvature away from the points: smallest radius {_rk.min():.4f} units; vertices with radius < 0.05: '
      f'{int((_rk < 0.05).sum())}, < 0.1: {int((_rk < 0.1).sum())} (of {len(_rk)})')
print(f'smallest gap between different arcs (or an arc and the line) farther than 0.5 from every point: '
      f'{MIN_GAP:.4f} units; 1st percentile {np.percentile(np.minimum(_gap, np.abs(_V[_far, 1])), 1):.4f}')
for p in range(F):   # every curve through p per the certificate has an arc ending at p in the drawing
    through = {bit(*e) for e in ARCS if p in ARCS[e]}
    assert len(through) == len(faces[p]) // 2

# ------------------------------------------------------------------ verification 2: raster read-back
def raster_labels(x0, y0, size, res):
    px = size / res
    lab = np.zeros((res, res), np.uint16)
    for j, c in enumerate(curves):
        a, b = c[:-1], c[1:]
        ylo = np.minimum(a[:, 1], b[:, 1]); yhi = np.maximum(a[:, 1], b[:, 1])
        r0_ = np.clip(np.ceil((ylo - y0) / px - 0.5).astype(np.int64), 0, res)
        r1_ = np.clip(np.ceil((yhi - y0) / px - 0.5).astype(np.int64), 0, res)
        cnt = np.maximum(r1_ - r0_, 0)
        e = np.repeat(np.arange(len(a)), cnt)
        rows = np.repeat(r0_, cnt) + (np.arange(cnt.sum()) - np.repeat(np.cumsum(cnt) - cnt, cnt))
        yc = y0 + (rows + 0.5) * px
        t = (yc - a[e, 1]) / (b[e, 1] - a[e, 1])
        xc = a[e, 0] + t * (b[e, 0] - a[e, 0])
        cols = np.clip(np.ceil((xc - x0) / px - 0.5).astype(np.int64), 0, res)
        acc = np.zeros((res, res + 1), np.int32)
        np.add.at(acc, (rows, cols), 1)
        lab |= ((np.cumsum(acc, axis=1)[:, :res] & 1).astype(np.uint16) << j)
    return lab

from scipy import ndimage
RES = 6000
W = R_LINE if not CLOSED else R_CLOSE + 0.6
x0 = y0 = -W; size = 2 * W; px = size / RES
lab = raster_labels(x0, y0, size, RES)
found = set(int(v) for v in np.unique(lab))
st8 = np.ones((3, 3), int)
ncomp, refined = {}, {}
boxes = ndimage.find_objects(lab.astype(np.int32) + 1)
for v in found:
    sl = boxes[v]
    cl, _ = ndimage.label(lab[sl] == v, structure=st8)
    sizes = np.bincount(cl.ravel())[1:]
    ncomp[v] = int((sizes >= 25).sum())
    if ncomp[v] != 1:
        bx0 = x0 + sl[1].start * px; bx1 = x0 + sl[1].stop * px
        by0 = y0 + sl[0].start * px; by1 = y0 + sl[0].stop * px
        sz = max(bx1 - bx0, by1 - by0) * 1.1
        lab2 = raster_labels((bx0 + bx1) / 2 - sz / 2, (by0 + by1) / 2 - sz / 2, sz, 4000)
        cl2, _ = ndimage.label(lab2 == v, structure=st8)
        s2 = np.bincount(cl2.ravel())[1:]
        refined[v] = int((s2 >= 25).sum())
split = {v for v, c in ncomp.items() if c != 1}
still = {v: c for v, c in refined.items() if c != 1}
# global XOR between drawn (bounded-side) labels and certificate labels, from the region far up
corner = int(lab[RES - 1, RES // 2])
top_region = FIXED[0] if (FIXED[0] >> LINE & 1) == UPBIT else FIXED[1]
if CLOSED:
    top_region = FIXED[1] if top_region == FIXED[0] else FIXED[0]   # beyond the closing arc
XORM = corner ^ top_region
# every drawn arc separates exactly the two regions the certificate says: exact even-odd point test just off
# both sides of the middle of each drawn arc
def label_at(pt):
    v = 0
    for j, c in enumerate(curves):
        a, b = c[:-1], c[1:]
        hit = (a[:, 1] > pt[1]) != (b[:, 1] > pt[1])
        xc = a[hit, 0] + (pt[1] - a[hit, 1]) * (b[hit, 0] - a[hit, 0]) / (b[hit, 1] - a[hit, 1])
        v |= (int((xc > pt[0]).sum()) & 1) << j
    return v ^ XORM
side_bad = 0
for e, P in arc_xy.items():
    k = len(P) // 2
    t = P[k + 1] - P[k]; t = t / np.linalg.norm(t); nrm = np.array([-t[1], t[0]])
    mid = 0.5 * (P[k] + P[k + 1])
    got = {label_at(mid + 1e-6 * nrm), label_at(mid - 1e-6 * nrm)}
    if got != set(e):
        side_bad += 1
n_side = len(arc_xy)
if not CLOSED:     # the fixed arc of the line curve: both of its rays, beyond the end points
    for sgn in (1.0, -1.0):
        mid = np.array([sgn * (XM + 0.5 * (RMAX - XM) + 0.3), 0.0])
        if {label_at(mid + [0, 1e-6]), label_at(mid - [0, 1e-6])} != set(FIXED):
            side_bad += 1
        n_side += 1
print(f'raster read-back ({RES} px): {len(found)}/256 masks present; {256 - len(split)} regions are one '
      f'component outright, {len(split)} needed a finer local raster {refined}; still split: {still}; '
      f'drawn label XOR certificate label = {XORM:08b} for every region; arcs whose two sides disagree with '
      f'the certificate: {side_bad}/{n_side}')
RASTER_OK = len(found) == N and not still and side_bad == 0
assert ((XORM >> LINE) & 1) == 0
if not (SEG_OK and RASTER_OK) and not os.environ.get('DEBUG'):
    raise SystemExit('verification failed')

# ------------------------------------------------------------------ render
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import Circle


def oklab_rgb(L, a, b):
    l_ = L + 0.3963377774 * a + 0.2158037573 * b
    m_ = L - 0.1055613458 * a - 0.0638541728 * b
    s_ = L - 0.0894841775 * a - 1.2914855480 * b
    l, m, s = l_ ** 3, m_ ** 3, s_ ** 3
    rgb = np.array([4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s,
                    -1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s,
                    -0.0041960863 * l - 0.7034186147 * m + 1.7076147010 * s])
    rgb = np.clip(rgb, 0, 1)
    return np.where(rgb <= 0.0031308, 12.92 * rgb, 1.055 * rgb ** (1 / 2.4) - 0.055)

# eight stroke colours, chosen apart in hue and lightness; the line curve is drawn in near-white
COL = ['#ff5d5d', '#ff9f1c', '#ffe14d', '#5ee06a', '#2fd8d0', '#4f9dff', '#c38bff', '#f1f1f1']
HUE = [25, 60, 100, 145, 195, 255, 305, None]
BG = '#0a0b10'
region_rgb = np.zeros((N, 3))
for x in range(N):
    js = [j for j in range(n) if x >> j & 1 and HUE[j] is not None]
    k = bin(x).count('1')
    if js:
        va = np.mean([math.cos(math.radians(HUE[j])) for j in js]); vb = np.mean([math.sin(math.radians(HUE[j])) for j in js])
        mag = math.hypot(va, vb); hue = math.atan2(vb, va) if mag > 1e-9 else 0.0
        chroma = 0.10 * min(1.0, 0.3 + 1.5 * mag)
    else:
        hue, chroma = 0.0, 0.0
    region_rgb[x] = oklab_rgb(0.20 + 0.055 * k, chroma * math.cos(hue), chroma * math.sin(hue))

half = (R_LINE if not CLOSED else R_CLOSE + 0.9)
bg_rgb = np.array([int(BG[i:i + 2], 16) for i in (1, 3, 5)]) / 255
OUTER_REGION = FIXED[1] if (FIXED[0] >> LINE & 1) == UPBIT else FIXED[0]      # region beyond the closing arc


def fill_image(px):
    """Region colours at px x px (each pixel by its drawn region); open version fades out beyond a viewing disc."""
    lab_ = raster_labels(-half, -half, 2 * half, px) ^ XORM
    pal = np.round(region_rgb * 255).astype(np.uint8)
    if CLOSED:
        pal[OUTER_REGION] = np.round(bg_rgb * 255).astype(np.uint8)
    im = pal[lab_]
    del lab_
    if not CLOSED:
        RV = RMAX + 0.9
        cc = (-half + (np.arange(px) + 0.5) * (2 * half / px)).astype(np.float32)
        am = np.clip((RV + 0.35 - np.sqrt(cc[:, None] ** 2 + cc[None, :] ** 2)) / 0.7, 0, 1)
        for ch in range(3):
            im[..., ch] = np.round(im[..., ch] * am + 255 * bg_rgb[ch] * (1 - am)).astype(np.uint8)
    return im


def render(path, px_fill, dpi):
    """Draw at 16 x 16 inches; stroke widths are set in output pixels of the 6000 px PNG."""
    fig = plt.figure(figsize=(16, 16), dpi=dpi)
    ax = fig.add_axes([0, 0, 1, 1]); ax.set_facecolor(BG); fig.patch.set_facecolor(BG)
    ax.imshow(fill_image(px_fill), origin='lower', extent=(-half, half, -half, half), interpolation='antialiased',
              zorder=0)
    pt = 72 / 375                     # one pixel of the 6000 px image, in points
    LWP, CASE, LW7 = 3.2 * pt, 4.6 * pt, 4.6 * pt     # min gap away from the points is about 5 px
    for j in range(n):
        c = curve_draw[j]
        ax.plot(c[:, 0], c[:, 1], color=BG, lw=(LW7 if j == LINE else LWP) + (CASE - LWP), alpha=0.6,
                solid_capstyle='round', solid_joinstyle='round', zorder=2)
    for j in range(n):
        c = curve_draw[j]
        if j == LINE and not CLOSED:
            # the line leaves the picture at both ends and closes through the point at infinity
            ax.plot([-(RMAX + 0.3), RMAX + 0.3], [0, 0], color=COL[j], lw=LW7, solid_capstyle='butt', zorder=3)
            xs_ = np.linspace(RMAX + 0.3, R_LINE - 0.2, 50)
            for sgn in (-1, 1):
                for k in range(len(xs_) - 1):
                    f = 1 - k / (len(xs_) - 1)
                    ax.plot(sgn * xs_[k:k + 2], [0, 0], color=COL[j], lw=LW7, alpha=f ** 1.4,
                            solid_capstyle='butt', zorder=3)
                ax.text(sgn * (R_LINE - 0.55), 0.32, '∞', color=TXT, fontsize=15, ha='center', va='bottom',
                        family='DejaVu Sans', zorder=4)
        else:
            ax.plot(c[:, 0], c[:, 1], color=COL[j], lw=LW7 if j == LINE else LWP, solid_capstyle='round',
                    solid_joinstyle='round', zorder=3)
    P = np.array([PT[p] for p in range(F)])
    ax.scatter(P[:, 0], P[:, 1], s=(9.5 * pt) ** 2, color='white', zorder=5, linewidths=0)
    ax.add_patch(Circle((0, 0), 0.2, facecolor='none', edgecolor='white', lw=6 * pt, zorder=6))
    ax.set_xlim(-half, half); ax.set_ylim(-half, half); ax.set_aspect('equal'); ax.axis('off')
    ax.text(0.02, 0.978, '8-Venn diagram, 37 crossing points', transform=ax.transAxes, color='#e2e5ec',
            fontsize=19, ha='left', va='top', family='DejaVu Sans')
    ax.text(0.02, 0.951, 'half-turn symmetric' if not CLOSED else 'half-turn symmetric except the closing arc',
            transform=ax.transAxes, color=TXT, fontsize=12.5, ha='left', va='top', family='DejaVu Sans')
    note = ('Rotating 180\u00b0 about the ringed point\nmaps the diagram to itself: curve j\ngoes to curve 6\u2212j '
            f'(j \u2264 6), curve {LINE} to {LINE}.\nCurve {LINE} (white) is the horizontal line;\nit closes through '
            '\u221e, the other centre.'
            if not CLOSED else
            f'Curve {LINE} (white) is the horizontal line\nclosed by the arc over the top, so all\neight curves are '
            'bounded. Rotating\n180\u00b0 about the ringed point maps\neverything else to itself.')
    ax.text(0.02, 0.022, note, transform=ax.transAxes, color=TXT, fontsize=10.5, ha='left', va='bottom',
            family='DejaVu Sans', linespacing=1.5)
    for j in range(n):
        yv = 0.03 + 0.024 * j
        ax.plot([0.925, 0.952], [yv, yv], transform=ax.transAxes, color=COL[j], lw=3.2, solid_capstyle='round')
        ax.text(0.962, yv, str(j), transform=ax.transAxes, color=TXT, fontsize=11.5, va='center')
    fig.savefig(path, facecolor=BG)
    plt.close(fig)
    print('wrote', path)


TXT = '#9aa0ad'
render(OUT, 6000, 375)
if '--pdf' in sys.argv:
    render(os.path.splitext(OUT)[0] + '.pdf', 2400, 150)
