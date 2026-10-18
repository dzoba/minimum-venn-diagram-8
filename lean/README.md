# Lean 4 check of the 37-crossing 8-Venn certificate

Kernel-checked statement about `../data/venn8_37_halfturn_a.json`
(sha256 `7c1fed92b696db20c8b5eb44fe4d3e03b098fcf0d12fa6b499c040108c41dd12`):

```lean
theorem Venn8.min_venn8_37 :
    (IsVennDual8 cert ∧ CrossingAtEachPoint cert) ∧ cert.length = 37 ∧
      ∀ fs : List Face, IsVennDual8 fs → 37 ≤ fs.length
```

The face list `cert` satisfies the combinatorial dual conditions of Brenner, Gregor, Mütze and Verciani (BGMV,
SoCG 2026, Section 1.3), at each of its points some two curves cross, it has 37 faces, and every face list
satisfying the dual conditions has at least 37 faces.

`#print axioms Venn8.min_venn8_37` gives `[propext, Classical.choice, Quot.sound]`, Lean's standard axioms. There
is no `sorry`, `admit` or `native_decide`. Every fact about the certificate is proved by `decide +kernel`, that is,
by evaluation in Lean's kernel. The trusted base is Lean's kernel and implementation and the three axioms above.

## What a reader has to check

1. **`Venn37/Defs.lean`**: the definitions below.
2. The **theorem statement** in `Venn37/Main.lean`, quoted above.
3. That **`Venn37/Cert.lean`** is the certificate. It is generated from the JSON face list by `gen_cert.py`, which
   checks the file's sha256; `python3 lean/gen_cert.py data/venn8_37_halfturn_a.json`, run from the repository
   root, rewrites `lean/Venn37/Cert.lean` byte for byte. The JSON's separate edge list is not used; edges are
   derived from the faces.

A face is the cyclic list of region labels around one crossing point. A label is a subset of the curves, written as
a number below 256 whose bit `i` is set when the region is inside curve `i` (curves are `0..7` here and in the
JSON; the paper numbers them `1..8`).

| field of `IsVennDual8` | meaning | BGMV |
|---|---|---|
| `q8` | every dart (consecutive pair in a face) is an edge of Q₈: both ends below 256, differing in one bit | subgraph of Q_n |
| `spanning` | all 256 labels occur | condition 1 |
| `balanced` | every face has length at least 4, and each direction occurs on it 0 or 2 times, so a face of length 2ℓ uses exactly two edges of each of ℓ directions | condition 2 |
| `paired` | no dart occurs twice, and the reverse of every dart occurs | plane |
| `links` | around every vertex the rotation visits all outgoing darts: vertex links are single cycles | plane |
| `connected` | the graph is connected | plane |
| `euler` | 256 − E + F = 2 | plane (sphere) |
| `curves` | for every curve j, the labels containing j and the labels not containing j each induce a connected subgraph | condition 3 |

`paired`, `links`, `connected` and `euler` together say that the face list is a combinatorial map (rotation
system) of the sphere; this is how "plane graph" is expressed.

`CrossingAtEachPoint fs` says that every face has two directions i ≠ k, each occurring twice, whose positions
interleave (pattern i…k…i…k): the two curves cross there rather than touch.

Connectivity (`InducedConnected`) is decided by growing a bitmask from the least label of the set for 256 rounds.
`Venn37/Sound.lean` proves this check sound: every label it reaches is joined to the start by a path of darts inside
the set (`reach_of_inducedConnected`).

## The lower bound (`Venn37/LowerBound.lean`)

`faces_ge_37 : IsVennDual8 fs → 37 ≤ fs.length` is a general proof, not a computation. Darts are twice the edges
(`paired`, no loops), darts are the sum of the face lengths, each face has length at most 16 (`balanced`), and
E = 254 + F (`euler`). So 508 + 2F ≤ 16F and F ≥ 37 = ⌈(2⁸ − 2)/7⌉.

## The half-turn (`cert_halfTurn`, not part of the main theorem)

`PreservesFaces cert halfTurn`: the map that swaps bits (0 6)(1 5)(2 4) and then XORs with 247 sends every face,
as a cyclic sequence with the same orientation, onto a face. Proved by `decide +kernel`.

## Scope

- Formalized: the dual conditions above for this face list, the crossing condition, and the counting bound for
  every face list satisfying the dual conditions.
- Not formalized, and cited: BGMV's characterization, that a plane spanning subgraph of Q_n with their conditions
  1–3 is the dual of an n-Venn diagram and conversely; and the step from a combinatorial map of the sphere to a
  drawing in the plane. The lower bound for all 8-Venn diagrams also uses the forward half of the
  characterization, that the dual of every 8-Venn diagram satisfies the conditions.

## Build

Toolchain `leanprover/lean4:v4.32.1` (`lean-toolchain`), Mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`
(`lakefile.lean`, `lake-manifest.json`). With elan installed:

```sh
cd lean
lake exe cache get
lake build
lake env lean AxiomAudit.lean     # prints the axioms and the statement; compare with AXIOMS.txt
```

**Memory.** `Venn37/CertProof.lean` peaks at about 15.8 GiB resident. `lake build` sets no memory cap and succeeds
on a machine with that much free memory. Under an 8 GiB cap it fails; a memory-limit kill is not a proof failure.
The independent rebuild compiled the modules one at a time in import order (Defs, Cert, Decide, Sound, LowerBound,
CertProof, Main, Venn37), with the Mathlib library directories on `LEAN_PATH` and `LEAN_NUM_THREADS=1`, using

```sh
lean -j1 -M16384 -DElab.async=false --tstack=4000000 -o <out>/Venn37/CertProof.olean Venn37/CertProof.lean
```

`CertProof.lean` took 324 CPU seconds on one core.

`Venn37/Eval.lean` and `Venn37/EvalCross.lean` are not part of the build. They evaluate the definitions with
`#eval` (`lake env lean Venn37/Eval.lean`): every condition is `true` on the certificate (37 faces, 582 darts, 291
edges); dropping a face breaks `euler` and `paired`; reversing a face breaks `paired` and `links`; XOR 1 is not an
automorphism; and there are 526 crossing and 475 touching curve pairs over the 37 points, as `ref37_v2.py` reports.

## Provenance

The `.lean` files, `gen_cert.py` and `lean-toolchain` are byte-identical to the author's development repository
at commit `35b00b4`. An independent review by Codex (OpenAI) rebuilt and reviewed commit `0eecb77`, whose `.lean`
files have the same SHA-256 hashes as these (`35b00b4` changed only the README). `AXIOMS.txt` is the output of
`AxiomAudit.lean` in that rebuild. This release was not rebuilt.

The only changes from `35b00b4` are in the Lake configuration: the development copy shared the Mathlib packages of
a sibling project through `packagesDir`; here `lakefile.lean` and `lake-manifest.json` use the default
`.lake/packages`. The Mathlib revision and the dependency pins are unchanged. This README is rewritten for the
release, and `AxiomAudit.lean` and `AXIOMS.txt` are added from the review.
