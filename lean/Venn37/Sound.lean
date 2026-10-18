/-
  Soundness of the connectivity check: if `InducedConnected fs S` holds, then every label `x < 256` with `S x` is
  joined to the seed by a path of darts that stays inside `S` (a reflexive-transitive closure in Mathlib's sense).
  So `InducedConnected` implies genuine connectivity of the subgraph induced by `S`.
-/
import Venn37.Defs

namespace Venn8

/-- One step inside `S`: a dart `u → v` with both ends in `S`. -/
def StepIn (fs : List Face) (S : ℕ → Bool) (u v : ℕ) : Prop := (u, v) ∈ darts fs ∧ S u = true ∧ S v = true

/-- `y` is reachable from `a` by a path of darts inside `S`. -/
def ReachIn (fs : List Face) (S : ℕ → Bool) (a y : ℕ) : Prop := Relation.ReflTransGen (StepIn fs S) a y

/-- The invariant of the growth: every bit set in the mask is in `S` and reachable from `a`. -/
def Good (fs : List Face) (S : ℕ → Bool) (a m : ℕ) : Prop := ∀ x, m.testBit x = true → S x = true ∧ ReachIn fs S a x

theorem good_foldl (fs : List Face) (S : ℕ → Bool) (a : ℕ) :
    ∀ (l : List (ℕ × ℕ)), (∀ d ∈ l, d ∈ darts fs) → ∀ m, Good fs S a m →
      Good fs S a (l.foldl (fun acc d => if acc.testBit d.1 && S d.2 then acc ||| (1 <<< d.2) else acc) m) := by
  intro l
  induction l with
  | nil => intro _ m hm; simpa using hm
  | cons d l ih =>
    intro hl m hm
    simp only [List.foldl_cons]
    apply ih (fun e he => hl e (List.mem_cons_of_mem d he))
    by_cases hc : (m.testBit d.1 && S d.2) = true
    · rw [if_pos hc]
      intro x hx
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · exact hm x hx
      · have hx' : d.2 = x := by simpa using hx
        subst hx'
        rw [Bool.and_eq_true] at hc
        obtain ⟨hS1, hR1⟩ := hm d.1 hc.1
        refine ⟨hc.2, Relation.ReflTransGen.tail hR1 ⟨?_, hS1, hc.2⟩⟩
        exact hl d List.mem_cons_self
    · rw [if_neg hc]; exact hm

theorem good_grow (fs : List Face) (S : ℕ → Bool) (a : ℕ) :
    ∀ k m, Good fs S a m → Good fs S a (grow fs S m k) := by
  intro k
  induction k with
  | zero => intro m hm; simpa [grow] using hm
  | succ k ih =>
    intro m hm
    simp only [grow]
    exact ih _ (good_foldl fs S a (darts fs) (fun d hd => hd) m hm)

/-- **Soundness.** If `InducedConnected fs S` holds and some label below 256 lies in `S`, then every label `x < 256`
in `S` is reachable from the seed by darts inside `S`; hence any two such labels are joined inside `S`. -/
theorem reach_of_inducedConnected (fs : List Face) (S : ℕ → Bool) (h : InducedConnected fs S)
    (hne : ∃ x < 256, S x = true) :
    ∀ x < 256, S x = true → ReachIn fs S (((List.range 256).find? S).getD 0) x := by
  intro x hx hSx
  set seed := ((List.range 256).find? S).getD 0 with hseed
  have hSseed : S seed = true := by
    obtain ⟨y, hy, hSy⟩ := hne
    have : ((List.range 256).find? S).isSome := by
      rw [List.find?_isSome]
      exact ⟨y, List.mem_range.mpr hy, hSy⟩
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp this
    rw [hseed, hs, Option.getD_some]
    exact List.find?_some hs
  have hstart : Good fs S seed (1 <<< seed) := by
    intro z hz
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow] at hz
    have : seed = z := by simpa using hz
    subst this
    exact ⟨hSseed, Relation.ReflTransGen.refl⟩
  exact (good_grow fs S seed 256 _ hstart x (h x hx hSx)).2

/-- Any two labels below 256 in `S` are joined by a path of darts inside `S` (in either direction, since a path
can be followed back through the seed when darts are paired; here stated as both reachable from the seed). -/
theorem joined_of_inducedConnected (fs : List Face) (S : ℕ → Bool) (h : InducedConnected fs S) :
    ∀ x < 256, ∀ y < 256, S x = true → S y = true →
      ∃ s, ReachIn fs S s x ∧ ReachIn fs S s y := by
  intro x hx y hy hSx hSy
  exact ⟨_, reach_of_inducedConnected fs S h ⟨x, hx, hSx⟩ x hx hSx,
    reach_of_inducedConnected fs S h ⟨x, hx, hSx⟩ y hy hSy⟩

end Venn8
