# Targeted negative controls

Two small inputs, each built so that exactly one of the conditions separating a Venn dual from a near miss fails.
They were constructed by the referee of this release (a separate Claude instance) and are copied here unchanged; the
`note` field in each file is the referee's. `checkers/run_all.py` requires every checker to reject both, and to give
the reason listed below; the results are in `logs/negative_controls.log`.

| file | n | what fails | everything else |
|---|---|---|---|
| `t05_curve3_two_circles.json` | 3 | condition 3 only: the regions inside curve 3 (bit 2) induce a disconnected subgraph, so curve 3 is two disjoint circles | a sphere map (V − E + F = 8 − 10 + 4 = 2) with a simple dual, all 8 labels once, balanced simple faces, and a crossing pair at every point |
| `t01_two_spheres_pinched_at_0_and_15.json` | 4 | vertex links only: two sphere maps glued at the labels 0 and 15, so each of these labels is two regions | V − E + F = 16 − 20 + 6 = 2, all 16 labels, balanced simple faces, connected, and condition 3 holds for every curve |

Expected reasons (substrings of the checkers' output):

| file | `check_a.py` | `check_b.py` | `ref37_v2.py` |
|---|---|---|---|
| `t05_curve3_two_circles.json` | `curve 2: a half is disconnected` | `curve 2: not a single closed curve` | `BGMV cond 3: curve 2 side 1 not connected` |
| `t01_two_spheres_pinched_at_0_and_15.json` | `corners do not form one rotation cycle` | `corners are not one disk` | `vertex link` failure (`2 vertices have a link that is not a single cycle`) |

On `t01`, `check_b.py` and `ref37_v2.py` also report that the curves are not single closed curves, and
`check_b.py` that its graph on the crossings is disconnected. Both programs follow the primal diagram through the
crossings, and the primal of this input falls apart at the two pinched vertices; on a map of the sphere their curve
test is equivalent to condition 3. `check_a.py` reports only the vertex links.
