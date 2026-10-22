# A minimum Venn diagram of order eight

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23464444.svg)](https://doi.org/10.5281/zenodo.23464444)

Paper, certificates, checkers and Lean proof for **A minimum Venn diagram of order eight**, Chris Dzoba (2026).

## The result

An 8-Venn diagram with 37 crossings. Every 8-Venn diagram has at least ⌈(2⁸ − 2)/7⌉ = 37 crossings (Bultena and
Ruskey, 1998), so 37 is the minimum. This settles n = 8, the first open case of Bultena and Ruskey's conjecture that
the bound is attained for all n ≥ 8, and answers the question of Brenner, Gregor, Mütze and Verciani (BGMV, SoCG
2026), whose construction has 40 crossings. The best diagram known before had 39 crossings (Seamons, Zenodo, August
2026).

The diagram is not simple: several curves pass through one crossing (32 of the 37 crossings lie on all eight
curves, five on seven). Following BGMV, at every crossing at least two curves cross; other curves may touch there.
The certificate is the dual graph in BGMV's characterization (Section 1.3 of their paper): a spanning plane subgraph
of the 8-cube whose faces are the crossings. BGMV state the direction "such a subgraph is the dual of a Venn
diagram" without proof; the paper proves it (Section 2) and prints the 37 faces in an appendix.

Also in this repository:
- a second 37-crossing diagram, not isomorphic to the first;
- the symmetry: both have a half-turn, and in every 8-Venn diagram with 37 crossings a finite group of
  orientation-preserving symmetries has order at most 2. Equivalently, at most two label maps x ↦ π(x) △ c that
  preserve the orientation of the faces map the face list onto itself, since such a group of label maps is realized
  by a finite group of homeomorphisms. For the two diagrams here a search finds exactly two automorphisms, the
  identity and the half-turn, with no orientation-reversing ones; for diagrams with 37 crossings in general the
  paper excludes reflections in outline only;
- a 9-Venn diagram with 74 crossings (BGMV's table lists 80), obtained by BGMV's doubling lemma (Lemma 10 of the
  SoCG 2026 version, Lemma 11 of arXiv:2511.09230v1) and optimal among 9-Venn diagrams in which some curve meets
  every other curve exactly twice; the general lower bound for n = 9 is still 64;
- doubled diagrams for 10 ≤ n ≤ 15 with 37·2ⁿ⁻⁸ crossings, checked only by the programs here;
- (new in v1.1) a 9-Venn diagram with 73 crossings, `data/venn9_73.json`, obtained by a two-tube doubling of the two
  37-crossing diagrams. It is the only diagram at F = 73 in the searched family (up to isomorphism), and none with
  F = 72 exists in that family. This is an upper bound only; the lower bound for n = 9 is still 64;
- (new in v1.1) its BGMV doublings for 10 ≤ n ≤ 15 with 73·2ⁿ⁻⁹ crossings: 146, 292, 584, 1168, 2336 and 4672.

## What was checked, and by what

| file | n | crossings | check_a | check_b | ref37_v2 | also |
|---|---|---|---|---|---|---|
| `data/venn8_37_halfturn_a.json` | 8 | 37 | PASS | PASS | PASS | Lean proof (see Lean below) |
| `data/venn8_37_halfturn_b.json` | 8 | 37 | PASS | PASS | PASS | none |
| `data/venn9_74.json` | 9 | 74 | PASS | PASS | PASS | doubling of `venn8_37_halfturn_a` |
| `data/venn9_74_mixed_r2.json` | 9 | 74 | PASS | PASS | PASS | none |
| `data/venn9_74_k3_nearmiss.json` | 9 | 74 | PASS | PASS | PASS | none |
| `data/venn10_148.json` … `data/venn15_4736.json` | 10–15 | 148 … 4736 | PASS | PASS | PASS | each is the doubling of the previous file |
| `data/venn9_73.json` | 9 | 73 | PASS | PASS | PASS | two-tube doubling of the two 37s |
| `data/venn10_146.json` … `data/venn15_4672.json` | 10–15 | 146 … 4672 | PASS | PASS | PASS | each is the doubling of the previous file |
| `calibration/venn8_39_crossing_candidate.json` | 8 | 39 | PASS | PASS | PASS | Seamons's 39 |
| `calibration/venn8_40_source_variant030.json` | 8 | 40 | PASS | PASS | PASS | Seamons's reconstruction of BGMV's 40 |

The three checkers were written separately, and none imports another. `check_a.py` checks BGMV's conditions 1–3
directly, plus the rotation system the faces induce and Euler's formula. `check_b.py` builds the primal diagram:
oriented 2-cell embedding, vertex links, and each curve one closed curve through the crossings. Claude wrote both.
`ref37_v2.py` was written from scratch from BGMV's definition by a separate Claude instance acting as referee; it
also checks that some pair of curves crosses at every crossing.

Every checker rejects every file above with one face removed, `venn8_37_halfturn_a.json` with a face reversed or
with two labels merged, and two targeted controls in `checkers/negative/`, built by the referee of this release, in
each of which exactly one condition fails: condition 3 (`t05`, n = 3, one curve is two circles) or the vertex
links (`t01`, n = 4, two sphere maps glued at two labels). On these two, `run_all.py` also requires each checker to
give the expected reason. See `logs/negative_controls.log` and `checkers/negative/README.md`.

Not part of this repository, and so not evidence a reader can rerun: Codex (OpenAI) wrote two further checkers and
a reconstruction of the first diagram, which accepted both 37-crossing diagrams and the three 74-crossing ones, and
compiled the full Lean project (see Lean below). Codex's checkers also accepted the 73-crossing diagram and the
146-crossing one, and Codex rebuilt the 73-crossing diagram independently from the stated construction, without the
producing code, reproducing every face and edge.

The name `venn9_74_k3_nearmiss` comes from the search, which was looking for a 73 in a particular class; the file is a
valid 74-crossing diagram. In the v1.0 files, the `provenance` field of each doubled file names the file it was
doubled from, with its SHA-256. In the v1.1 files it records the construction parameters of the 73 (the two 37s, the
face paths, the rungs and the relabelling) and, for each doubling, the provenance of the file it was doubled from,
without SHA-256s. `checkers/invariants.py` checks both doubling chains face by face.

## Changes in v1.1

- Added `data/venn9_73.json`, a 9-Venn diagram with 73 crossings (two-tube doubling of the two 37-crossing diagrams),
  and its doublings `data/venn10_146.json`, `data/venn11_292.json`, `data/venn12_584.json`,
  `data/venn13_1168.json`, `data/venn14_2336.json` and `data/venn15_4672.json`. All seven pass `check_a.py`,
  `check_b.py` and `ref37_v2.py`; the logs are in `logs/`.
- These are upper bounds only. The lower bound for n = 9 is 64 and the paper makes no optimality claim there. The
  74-crossing optimality statement is unchanged: it concerns diagrams in which some curve meets every other curve
  exactly twice.
- `paper/venn37.tex` and `paper/venn37.pdf` gain a paragraph describing the construction and the census, a table row,
  and a changed sentence on local searches (they found no 73, but the two-tube doubling does). The paper is now 7
  pages, the last being the appendix.
- Nothing was removed. The 37-crossing certificates, the 74 and 148 … 4736 files and the Lean project are as in v1.0.

## Check it

Python 3, standard library only, about 30 seconds, from the repository root:

```sh
python3 checkers/run_all.py
```

It runs the three checkers on every file in `data/` and `calibration/` and the negative controls, rewrites `logs/`,
and prints `ALL REQUIREMENTS MET` (exit status 0) when everything passes and every control is rejected (with the
expected reason, for the two targeted controls). The
committed logs are from the packaging run; a rerun changes their timestamps, so `shasum -a 256 -c SHA256SUMS` will
then report the logs as changed. A single file
is checked with `python3 checkers/check_a.py data/venn8_37_halfturn_a.json`, and likewise for the other two.

`python3 checkers/invariants.py` prints the numbers quoted in the paper (face lengths, crossings per curve, degree
sequences, the full automorphism group of each 8-curve file, meeting counts at n = 9, and the doubling chain); its
output is `logs/invariants.log`. It is not a validity checker.

## File format

JSON with keys `n`, `edges` and `faces`. Each face is `{"vertices": [...]}`, the cyclic list of region labels
around one crossing; a region label is an integer whose bit i − 1 is set when the region is inside curve i. The
faces alone determine the diagram; `edges` lists `[u, v, direction]` for convenience. The paper numbers curves 1 to
8; the files, the Lean code and the figure legend use bits 0 to 7.

## Contents

- `paper/venn37.tex`, `paper/venn37.pdf`: the paper (7 pages; the last is the appendix listing the 37 faces).
  `paper/venn8_37.jpg` is the figure, a 3000-pixel copy of the output of `paper/render37.py`, which draws the
  diagram from the certificate and checks the drawing against it.
- `data/`: the certificates, with `data/SHA256SUMS`.
- `calibration/`: Seamons's 39 and his reconstruction of BGMV's 40, CC BY 4.0 (see `calibration/README.md`).
- `checkers/`: `check_a.py`, `check_b.py`, `ref37_v2.py`, `run_all.py`, `invariants.py`; `checkers/negative/`, the
  two targeted negative controls with a note.
- `logs/`: one log per certificate (all three checkers, with exit status and SHA-256 of inputs and checkers),
  `negative_controls.log`, `invariants.log`, `SUMMARY.log`.
- `lean/`: Lean 4 project, source only.
- `SHA256SUMS`: checksums of every file, excluding itself.

## Lean

`lean/` proves, for the face list `cert` of `data/venn8_37_halfturn_a.json`,

```lean
theorem Venn8.min_venn8_37 :
    (IsVennDual8 cert ∧ CrossingAtEachPoint cert) ∧ cert.length = 37 ∧
      ∀ fs : List Face, IsVennDual8 fs → 37 ≤ fs.length
```

with axioms `propext`, `Classical.choice` and `Quot.sound` only (`lean/AXIOMS.txt`), by `decide +kernel` and no
`native_decide`. BGMV's characterization (the converse direction is proved in the paper) and the step from a
combinatorial map of the sphere to a plane drawing are not formalized. Toolchain `leanprover/lean4:v4.32.1`, Mathlib
`520045ab`:

```sh
cd lean
lake exe cache get
lake build
```

The build needs about 16 GiB of memory; see `lean/README.md` for the definitions, the scope, and a per-module
command for machines where `lake build` runs out of memory.

What has been built: from this directory exactly as released, `lake exe cache get` resolves the pinned
dependencies and the modules `Defs`, `Cert`, `Decide`, `LowerBound` and `Sound` build, and the bound
`faces_ge_37` uses only the three axioms above. `CertProof` (the 16 GiB kernel evaluation of the certificate), and
so `Main`, has not been built in this configuration. Codex compiled the whole project, `CertProof` included, from
the same `.lean` files under a different Lake configuration (a shared package directory); `lean/AXIOMS.txt` is the
axiom report from that build, whose log is not included. Details in `lean/README.md`.

## Draw the figure

```sh
mkdir -p build
uv run --with numpy --with matplotlib --with scipy python paper/render37.py data/venn8_37_halfturn_a.json build/venn8_37_closed.png --closed
```

The relaxation takes about 10 minutes. The script exits with an error if the drawing does not match the certificate.

## Build the paper

```sh
cd paper
tectonic venn37.tex
```

## References

- B. Bultena and F. Ruskey, Venn diagrams with few vertices, Electron. J. Combin. 5 (1998), #R44.
- S. Brenner, P. Gregor, T. Mütze and F. Verciani, On minimum Venn diagrams, SoCG 2026, LIPIcs 367, 21:1–21:18;
  arXiv:2511.09230.
- J. Seamons, A 39-crossing Venn diagram of order eight, Zenodo (2026), https://doi.org/10.5281/zenodo.22004839.

## How to cite

Chris Dzoba, *A minimum Venn diagram of order eight*, 2026. Zenodo, https://doi.org/10.5281/zenodo.23464444 (code, data and paper; GitHub: https://github.com/dzoba/minimum-venn-diagram-8)

## License

Code, including the checkers, the Lean formalization and the drawing script, is licensed under MIT; see
`LICENSE-CODE`. The paper, figure, documentation and data are licensed under Creative Commons Attribution 4.0
International; see `LICENSE-PAPER-DATA`. The files in `calibration/` are John Seamons's, under CC BY 4.0. Dependency
licenses remain their own.
