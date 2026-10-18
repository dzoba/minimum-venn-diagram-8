/-
  The counting lower bound: every face list satisfying the BGMV dual conditions for n = 8 has at least 37 faces.

  E = 254 + F (Euler with V = 256), 2E = (sum of face lengths) ≤ 16F, hence 508 + 2F ≤ 16F and F ≥ 37.
-/
import Venn37.Defs

namespace Venn8

theorem length_faceDarts (f : Face) : (faceDarts f).length = f.length := by
  simp [faceDarts, List.length_zip, List.length_rotate]

theorem length_darts (fs : List Face) : (darts fs).length = (fs.map List.length).sum := by
  simp only [darts, List.length_flatMap]
  congr 1
  exact List.map_congr_left (fun f _ => length_faceDarts f)

/-- If every element of `l` lies in exactly one of the 8 direction classes, then `l.length` is the sum of the class
counts. -/
theorem length_eq_sum_countP (l : List (ℕ × ℕ)) (h : ∀ d ∈ l, ∃ i < 8, d.1 ^^^ d.2 = 2 ^ i) :
    l.length = ∑ i ∈ Finset.range 8, l.countP (fun d => d.1 ^^^ d.2 = 2 ^ i) := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have hl : ∀ e ∈ l, ∃ i < 8, e.1 ^^^ e.2 = 2 ^ i := fun e he => h e (List.mem_cons_of_mem d he)
    obtain ⟨i₀, hi₀, hd⟩ := h d List.mem_cons_self
    simp only [List.countP_cons, List.length_cons, Finset.sum_add_distrib, ← ih hl]
    congr 1
    have : ∀ i ∈ Finset.range 8, (if decide (d.1 ^^^ d.2 = 2 ^ i) = true then 1 else 0) =
        (if i₀ = i then 1 else 0) := by
      intro i _
      rw [hd]
      by_cases h' : i₀ = i
      · simp [h']
      · have : (2 : ℕ) ^ i₀ ≠ 2 ^ i := fun e => h' (Nat.pow_right_injective le_rfl e)
        simp [h', this]
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp [Finset.mem_range.mpr hi₀]

theorem face_length_le (fs : List Face) (hq : Q8Subgraph fs) (hb : FacesBalanced fs) :
    ∀ f ∈ fs, f.length ≤ 16 := by
  intro f hf
  have hdir : ∀ d ∈ faceDarts f, ∃ i < 8, d.1 ^^^ d.2 = 2 ^ i := by
    intro d hd
    obtain ⟨i, hi, -, -, -, he⟩ := hq d (List.mem_flatMap.mpr ⟨f, hf, hd⟩)
    exact ⟨i, hi, he⟩
  rw [← length_faceDarts, length_eq_sum_countP _ hdir]
  calc ∑ i ∈ Finset.range 8, (faceDarts f).countP (fun d => d.1 ^^^ d.2 = 2 ^ i)
      ≤ ∑ _i ∈ Finset.range 8, 2 := by
        apply Finset.sum_le_sum
        intro i hi
        rcases (hb f hf).2 i (Finset.mem_range.mp hi) with h0 | h2 <;> omega
    _ = 16 := by simp

/-- With paired darts and no loops, the number of darts is twice the number of undirected edges. -/
theorem darts_length_eq (fs : List Face) (hq : Q8Subgraph fs) (hp : DartsPaired fs) :
    (darts fs).length = 2 * (edges fs).length := by
  obtain ⟨hnd, hsw⟩ := hp
  have hne : ∀ d ∈ darts fs, d.1 ≠ d.2 := by
    intro d hd heq
    obtain ⟨i, -, -, -, -, he⟩ := hq d hd
    rw [heq, Nat.xor_self] at he
    exact absurd he.symm (pow_ne_zero i (by norm_num))
  set A := (darts fs).filter (fun d => d.1 < d.2) with hA
  set B := (darts fs).filter (fun d => !decide (d.1 < d.2)) with hB
  have hsplit : (darts fs).length = A.length + B.length := by
    rw [hA, hB]
    exact List.length_eq_length_filter_add (fun d : ℕ × ℕ => decide (d.1 < d.2))
  have hAnd : A.Nodup := hnd.filter _
  have hBnd : B.Nodup := hnd.filter _
  have hAB : (A.map Prod.swap) ⊆ B := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [hA, List.mem_filter] at hd
    rw [hB, List.mem_filter]
    refine ⟨hsw d hd.1, ?_⟩
    simp only [Prod.fst_swap, Prod.snd_swap, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hd ⊢
    omega
  have hBA : (B.map Prod.swap) ⊆ A := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    rw [hB, List.mem_filter] at hd
    rw [hA, List.mem_filter]
    refine ⟨hsw d hd.1, ?_⟩
    have := hne d hd.1
    simp only [Prod.fst_swap, Prod.snd_swap, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hd ⊢
    omega
  have h1 : A.length ≤ B.length := by
    simpa using (List.subperm_of_subset (hAnd.map Prod.swap_injective) hAB).length_le
  have h2 : B.length ≤ A.length := by
    simpa using (List.subperm_of_subset (hBnd.map Prod.swap_injective) hBA).length_le
  have : edges fs = A := rfl
  rw [this]
  omega

/-- **Lower bound.** Every oriented face list satisfying the BGMV dual conditions for an 8-Venn diagram has at least
37 faces (= ⌈(2⁸ − 2)/7⌉). Only the hypercube, balanced-face, dart-pairing and Euler conditions are used. -/
theorem faces_ge_37 (fs : List Face) (h : IsVennDual8 fs) : 37 ≤ fs.length := by
  have hE := darts_length_eq fs h.q8 h.paired
  have hsum := length_darts fs
  have hle : (fs.map List.length).sum ≤ 16 * fs.length := by
    have := List.sum_le_card_nsmul (fs.map List.length) 16 (by
      intro x hx
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hx
      exact face_length_le fs h.q8 h.balanced f hf)
    simpa [mul_comm] using this
  have heu := h.euler
  unfold EulerSphere at heu
  omega

end Venn8
