/-
  The combinatorial dual conditions for 8-Venn diagrams (Brenner, Gregor, Mütze, Verciani, "On Minimum Venn
  Diagrams", SoCG 2026, arXiv:2511.09230, Section 1.3), stated for an oriented face list. This is the file a reader
  has to check.

  A candidate dual is given by its faces. Each face is the cyclic list of region labels met in order around one
  crossing point. A region label is a subset of the curves {0, …, 7}, written as a number below 256 (bit i set iff
  the region lies inside curve i). The edges of the dual are the consecutive pairs in the faces.

  BGMV's characterization (cited, not formalized here): a plane spanning subgraph of Q_n satisfying conditions 1–3
  is the dual of an n-Venn diagram, and conversely. `IsVennDual8` below states condition 1 (spanning), condition 2
  (plane, with direction-balanced faces), condition 3 (both halves of every curve connected), and, for "plane", that
  the face list is a combinatorial map of the sphere (darts paired, vertex links single cycles, connected,
  V − E + F = 2).
-/
import Mathlib

namespace Venn8

/-- A face: the cyclic list of region labels around one crossing point. -/
abbrev Face := List ℕ

/-- The darts (directed edges) of a face, `(v₀,v₁), (v₁,v₂), …, (v_{L-1},v₀)`. -/
def faceDarts (f : Face) : List (ℕ × ℕ) := List.zip f (f.rotate 1)

/-- All darts of a face list. -/
def darts (fs : List Face) : List (ℕ × ℕ) := fs.flatMap faceDarts

/-- `d` is an edge of the hypercube `Q₈` in direction `i`: both ends are labels below 256 and they differ exactly in
bit `i`. -/
def IsQ8Edge (d : ℕ × ℕ) (i : ℕ) : Prop := d.1 < 256 ∧ d.2 < 256 ∧ i < 8 ∧ d.1 ^^^ d.2 = 2 ^ i

/-- The undirected edges: each pair of opposite darts is counted once (by its dart `(u,v)` with `u < v`). -/
def edges (fs : List Face) : List (ℕ × ℕ) := (darts fs).filter (fun d => d.1 < d.2)

/-! ### Condition 1: a spanning subgraph of `Q₈` -/

/-- Every dart is an edge of `Q₈`. -/
def Q8Subgraph (fs : List Face) : Prop := ∀ d ∈ darts fs, ∃ i < 8, IsQ8Edge d i

/-- All 256 labels occur (the subgraph is spanning; the vertex set is exactly `{0, …, 255}`). -/
def Spanning (fs : List Face) : Prop := ∀ x < 256, ∃ f ∈ fs, x ∈ f

/-! ### Condition 2: faces of length 2ℓ use exactly two edges of each of ℓ directions -/

/-- Every face has length at least 4, and each direction occurs on it either 0 or exactly 2 times. (With every dart
an edge of `Q₈`, a face of length 2ℓ then uses exactly two edges of each of ℓ distinct directions, 2 ≤ ℓ ≤ 8.) -/
def FacesBalanced (fs : List Face) : Prop :=
  ∀ f ∈ fs, 4 ≤ f.length ∧
    ∀ i < 8, ((faceDarts f).countP (fun d => d.1 ^^^ d.2 = 2 ^ i) = 0 ∨
              (faceDarts f).countP (fun d => d.1 ^^^ d.2 = 2 ^ i) = 2)

/-! ### "Plane": the face list is a combinatorial map of the sphere -/

/-- Darts are paired: no dart occurs twice, and the reverse of every dart occurs. -/
def DartsPaired (fs : List Face) : Prop := (darts fs).Nodup ∧ ∀ d ∈ darts fs, d.swap ∈ darts fs

/-- For each dart `v → w` in a face, the label `p` preceding `v` in that face (`p → v → w`). -/
def prevTable (fs : List Face) : List ((ℕ × ℕ) × ℕ) :=
  fs.flatMap fun f => List.zip (faceDarts f) (f.rotate (f.length - 1))

/-- The rotation around a vertex: after the dart `v → w`, the next dart around `v` is `v → p`, where `p → v → w` in
the face containing `v → w`. -/
def rotNext (fs : List Face) (d : ℕ × ℕ) : ℕ × ℕ := (d.1, ((prevTable fs).lookup d).getD d.2)

/-- The darts leaving `v`. -/
def outDarts (fs : List Face) (v : ℕ) : List (ℕ × ℕ) := (darts fs).filter (fun d => d.1 = v)

/-- Vertex links are single cycles: around every vertex, the rotation started at the first outgoing dart reaches
every outgoing dart within (number of outgoing darts) steps. (With paired darts the rotation is a permutation of the
outgoing darts, so this says it is a single cycle: no pinched vertices.) -/
def LinksSingleCycles (fs : List Face) : Prop :=
  ∀ v < 256, ∀ e ∈ outDarts fs v,
    ∃ k < (outDarts fs v).length, (rotNext fs)^[k] ((outDarts fs v).headD (v, v)) = e

/-- One round of growing a set of labels (a bitmask) along darts, staying inside `S`. -/
def growStep (fs : List Face) (S : ℕ → Bool) (m : ℕ) : ℕ :=
  (darts fs).foldl (fun acc d => if acc.testBit d.1 && S d.2 then acc ||| (1 <<< d.2) else acc) m

/-- `k` rounds of growing. -/
def grow (fs : List Face) (S : ℕ → Bool) : ℕ → ℕ → ℕ
  | m, 0 => m
  | m, k + 1 => grow fs S (growStep fs S m) k

/-- The labels `x < 256` with `S x` induce a connected subgraph: growing from the least such label along darts
inside `S` for 256 rounds reaches every one of them. (A path in a graph on at most 256 vertices has fewer than 256
edges; `Venn37.Sound` proves that every label reached is joined to the start by a path inside `S`.) -/
def InducedConnected (fs : List Face) (S : ℕ → Bool) : Prop :=
  let seed := ((List.range 256).find? S).getD 0
  ∀ x < 256, S x = true → (grow fs S (1 <<< seed) 256).testBit x = true

/-- The graph is connected. -/
def Connected (fs : List Face) : Prop := InducedConnected fs (fun _ => true)

/-- Euler's formula for the sphere, with V = 256 (by `Spanning` and `Q8Subgraph` the labels are exactly
`{0, …, 255}`), E = number of undirected edges, F = number of faces. -/
def EulerSphere (fs : List Face) : Prop := (256 : ℤ) - (edges fs).length + fs.length = 2

/-! ### Condition 3: both halves of every curve are connected -/

/-- For every curve `j`, the labels containing `j` and the labels not containing `j` each induce connected
subgraphs. -/
def CurvesSimple (fs : List Face) : Prop :=
  ∀ j < 8, InducedConnected fs (fun x => x.testBit j) ∧ InducedConnected fs (fun x => !x.testBit j)

/-- **The BGMV dual conditions for an 8-Venn diagram**, for an oriented face list. -/
structure IsVennDual8 (fs : List Face) : Prop where
  q8 : Q8Subgraph fs
  spanning : Spanning fs
  balanced : FacesBalanced fs
  paired : DartsPaired fs
  links : LinksSingleCycles fs
  connected : Connected fs
  euler : EulerSphere fs
  curves : CurvesSimple fs

/-! ### At every crossing point at least two curves cross (BGMV's definition of a Venn diagram) -/

/-- The positions (indices `0, …, L−1` in the face's dart list) of the darts of direction `i`. -/
def dirPositions (f : Face) (i : ℕ) : List ℕ :=
  (List.range f.length).filter fun j =>
    ((faceDarts f).getD j (0, 0)).1 ^^^ ((faceDarts f).getD j (0, 0)).2 = 2 ^ i

/-- Curves `i` and `k` cross (not merely touch) at the point of face `f`: each has exactly two darts on `f`, and
their positions interleave around the face, i.e. exactly one dart of `k` lies strictly between the two darts of `i`
(pattern i…k…i…k, not i…i…k…k). Interleaving of linear positions is the same as interleaving in cyclic order. -/
def CrossAt (f : Face) (i k : ℕ) : Prop :=
  (dirPositions f i).length = 2 ∧ (dirPositions f k).length = 2 ∧
    (((dirPositions f i).getD 0 0 < (dirPositions f k).getD 0 0 ∧
        (dirPositions f k).getD 0 0 < (dirPositions f i).getD 1 0) ↔
      ¬ ((dirPositions f i).getD 0 0 < (dirPositions f k).getD 1 0 ∧
        (dirPositions f k).getD 1 0 < (dirPositions f i).getD 1 0))

/-- At every crossing point (face) some two curves cross. -/
def CrossingAtEachPoint (fs : List Face) : Prop := ∀ f ∈ fs, ∃ i < 8, ∃ k < 8, i ≠ k ∧ CrossAt f i k

/-! ### The half-turn -/

/-- The half-turn of the 37 certificate: swap curves (0 6)(1 5)(2 4), then complement (XOR 247 = 0b11110111). -/
def halfTurn (x : ℕ) : ℕ :=
  let b := fun i => if x.testBit i then 2 ^ i else 0
  (b 6 / 2 ^ 6 * 1 + b 5 / 2 ^ 5 * 2 + b 4 / 2 ^ 4 * 4 + b 3 + b 2 / 4 * 16 + b 1 / 2 * 32 + b 0 * 64 + b 7) ^^^ 247

/-- A map `g` of labels is an orientation-preserving automorphism of the face list: it maps every face, as a cyclic
sequence, onto some face. -/
def PreservesFaces (fs : List Face) (g : ℕ → ℕ) : Prop :=
  ∀ f ∈ fs, ∃ f' ∈ fs, ∃ k < f'.length, f.map g = f'.rotate k

end Venn8
