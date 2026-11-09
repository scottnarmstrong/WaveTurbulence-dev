/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.Bonds

/-!
# N1 Lemma D: 2-cut decoupling

Research note N1 §2.2 (`research-gamma-half/NOTES.md` L142–L168; REFEREED, REF1 claim 2), for a block `S` with
joints `a` (flow `−r`) and `b` (flow `r`) of a molecule, and two bonds `ℓ, ℓ'` whose removal separates a side `Y`:

* **one in, one out** (`lemmaD_oneInOneOut`): relative to `Y`, one of `ℓ, ℓ'` enters and the other leaves;
* **the gap** (`lemmaD_gap`): on the fiber, `k_ℓ − k_ℓ' = Σ_{w ∈ Y} c_w ∈ {0, ±r}` (`ℓ` the leaving bond);
* **decoupling** (`lemmaD_splice`, `flow_add_const`): two fiber elements agreeing on `ℓ, ℓ'` can be spliced
  across the cut (the solution set is the product of the two sides), and each conservation law at a balanced atom
  is invariant under adding one vector to all labels (the `δ`-system of N1);
* **the quadratic forms** (`energy_add_const`, `energy_balanced`): at a balanced atom with conservation the energy
  is invariant under such a shift, and at a degree-4 atom with outgoing `o₁, o₂` and incoming `i₁, i₂` it is
  `−2⟨k_{o₁} − k_{i₁}, k_{o₁} − k_{i₂}⟩` (a function of differences of labels at the atom only).

Here "the side `Y`" is any `Y ⊆ S` such that `ℓ, ℓ'` are exactly the bonds of `S` with one end in `Y`.
Sign convention: energy `= Σ_in |k|² − Σ_out |k|²` (main's `VineParamContract.energy`; N1's `Γ_w` is its negative).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S : Finset V}

/-- The bond `e` has exactly one end in `Y`. -/
def Crosses (Y : Finset V) (e : Bond M S) : Prop := (tl e ∈ Y ∧ hd e ∉ Y) ∨ (hd e ∈ Y ∧ tl e ∉ Y)

/-- The `±1/0` crossing sign of a bond: `+1` leaving `Y`, `−1` entering, `0` otherwise. -/
def crossSign (Y : Finset V) (e : Bond M S) : ℤ := (if tl e ∈ Y then 1 else 0) - (if hd e ∈ Y then 1 else 0)

theorem crossSign_eq_zero {Y : Finset V} {e : Bond M S} (h : ¬ Crosses Y e) : crossSign Y e = 0 := by
  unfold Crosses at h; unfold crossSign
  by_cases h1 : tl e ∈ Y <;> by_cases h2 : hd e ∈ Y <;> simp_all

/-- On a block of a molecule, the crossing signs of all bonds sum to zero (every atom is balanced). -/
theorem sum_crossSign (hM : M.IsMolecule) {a b : V} (hB : M.IsBlock S a b) {Y : Finset V} (hY : Y ⊆ S) :
    (∑ e : Bond M S, crossSign Y e) = 0 := by
  have h : (∑ v ∈ Y, ∑ e : Bond M S, incidence M v e.1) = 0 :=
    Finset.sum_eq_zero (fun v hv => sum_incidence_block hM hB (hY hv))
  rw [Finset.sum_comm] at h
  simpa only [sum_incidence_set, crossSign] using h

/-- **Lemma D, one in and one out.** -/
theorem lemmaD_oneInOneOut (hM : M.IsMolecule) {a b : V} (hB : M.IsBlock S a b) {Y : Finset V} (hY : Y ⊆ S)
    {ℓ ℓ' : Bond M S} (hne : ℓ ≠ ℓ') (hcut : ∀ e, Crosses Y e ↔ e = ℓ ∨ e = ℓ') :
    (tl ℓ ∈ Y ∧ hd ℓ ∉ Y ∧ hd ℓ' ∈ Y ∧ tl ℓ' ∉ Y) ∨ (hd ℓ ∈ Y ∧ tl ℓ ∉ Y ∧ tl ℓ' ∈ Y ∧ hd ℓ' ∉ Y) := by
  classical
  have hs := sum_crossSign hM hB hY
  have hrest : ∀ e ∈ (univ : Finset (Bond M S)), e ≠ ℓ → e ≠ ℓ' → crossSign Y e = 0 := by
    intro e _ h1 h2
    exact crossSign_eq_zero (fun h => by rcases (hcut e).mp h with h | h <;> contradiction)
  rw [← Finset.sum_subset (s₁ := {ℓ, ℓ'}) (subset_univ _)
    (fun e he hn => by
      simp only [mem_insert, mem_singleton, not_or] at hn
      exact hrest e he hn.1 hn.2)] at hs
  rw [Finset.sum_pair hne] at hs
  have c1 := (hcut ℓ).mpr (Or.inl rfl)
  have c2 := (hcut ℓ').mpr (Or.inr rfl)
  unfold crossSign at hs
  unfold Crosses at c1 c2
  rcases c1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases c2 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> simp_all

/-- **Lemma D, homogeneous form.** If all flows vanish, the two bonds crossing `Y` carry equal labels. -/
theorem lemmaD_homog (hM : M.IsMolecule) {a b : V} (hB : M.IsBlock S a b) {Y : Finset V} (hY : Y ⊆ S)
    {ℓ ℓ' : Bond M S} (hne : ℓ ≠ ℓ') (hcut : ∀ e, Crosses Y e ↔ e = ℓ ∨ e = ℓ') {E : Type*} [AddCommGroup E]
    (d : Bond M S → E) (hflow : ∀ v ∈ S, flow M S d v = 0) : d ℓ = d ℓ' := by
  classical
  have h1 := sum_flow_set (M := M) (S := S) Y d
  rw [Finset.sum_eq_zero (fun v hv => hflow v (hY hv))] at h1
  have hrest : ∀ e ∈ (univ : Finset (Bond M S)), e ∉ ({ℓ, ℓ'} : Finset (Bond M S)) →
      ((if tl e ∈ Y then (1 : ℤ) else 0) - (if hd e ∈ Y then 1 else 0)) • d e = 0 := by
    intro e _ hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    have := crossSign_eq_zero (Y := Y) (e := e)
      (fun h => by rcases (hcut e).mp h with h | h <;> simp_all)
    unfold crossSign at this
    rw [this, zero_smul]
  rw [← Finset.sum_subset (subset_univ _) hrest, Finset.sum_pair hne] at h1
  rcases lemmaD_oneInOneOut hM hB hY hne hcut with ⟨h2, h3, h4, h5⟩ | ⟨h2, h3, h4, h5⟩
  · simp only [h2, h3, h4, h5, ite_true, ite_false, sub_zero, zero_sub, one_smul, neg_smul] at h1
    rw [← sub_eq_zero, sub_eq_add_neg]; exact h1.symm
  · simp only [h2, h3, h4, h5, ite_true, ite_false, sub_zero, zero_sub, one_smul, neg_smul] at h1
    rw [← sub_eq_zero, ← neg_eq_zero, neg_sub, sub_eq_add_neg, add_comm]; exact h1.symm

/-- The fiber flow target of an atom of `S`. -/
theorem flow_fiber {E : Type*} [AddCommGroup E] {a b : V} {r : E} (hab : a ≠ b)
    (k : FlowFiber M S a b E r) {v : V} (hv : v ∈ S) :
    flow M S k.1 v = (if v = b then r else 0) - (if v = a then r else 0) := by
  by_cases ha : v = a
  · subst ha; rw [k.2.1]; simp [hab]
  by_cases hb : v = b
  · subst hb; rw [k.2.2.1]; simp [ha]
  rw [k.2.2.2 v hv ha hb]; simp [ha, hb]

/-- **Lemma D, the gap.** If `ℓ` leaves `Y` and `ℓ'` enters `Y`, and they are the only bonds crossing `Y`, then on
the fiber `k_ℓ − k_ℓ'` is the total source of `Y`: `r` if only `b ∈ Y`, `−r` if only `a ∈ Y`, else `0`. -/
theorem lemmaD_gap {E : Type*} [AddCommGroup E] {a b : V} {r : E} (hab : a ≠ b) {Y : Finset V} (hY : Y ⊆ S)
    {ℓ ℓ' : Bond M S} (hne : ℓ ≠ ℓ') (hcut : ∀ e, Crosses Y e ↔ e = ℓ ∨ e = ℓ')
    (hℓ : tl ℓ ∈ Y ∧ hd ℓ ∉ Y) (hℓ' : hd ℓ' ∈ Y ∧ tl ℓ' ∉ Y) (k : FlowFiber M S a b E r) :
    k.1 ℓ - k.1 ℓ' = (if b ∈ Y then r else 0) - (if a ∈ Y then r else 0) := by
  classical
  have h1 := sum_flow_set (M := M) (S := S) Y k.1
  have hrest : ∀ e ∈ (univ : Finset (Bond M S)), e ∉ ({ℓ, ℓ'} : Finset (Bond M S)) →
      ((if tl e ∈ Y then (1 : ℤ) else 0) - (if hd e ∈ Y then 1 else 0)) • k.1 e = 0 := by
    intro e _ hn
    simp only [mem_insert, mem_singleton, not_or] at hn
    have := crossSign_eq_zero (Y := Y) (e := e)
      (fun h => by rcases (hcut e).mp h with h | h <;> simp_all)
    unfold crossSign at this
    rw [this, zero_smul]
  rw [← Finset.sum_subset (subset_univ _) hrest, Finset.sum_pair hne] at h1
  simp only [hℓ.1, hℓ.2, hℓ'.1, hℓ'.2, ite_true, ite_false, sub_zero, zero_sub, one_smul, neg_smul] at h1
  rw [← sub_eq_add_neg] at h1
  rw [← h1]
  have h2 : (∑ v ∈ Y, flow M S k.1 v) = ∑ v ∈ Y, ((if v = b then r else 0) - (if v = a then r else 0)) :=
    Finset.sum_congr rfl (fun v hv => flow_fiber hab k (hY hv))
  rw [h2, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

/-- **Lemma D, decoupling (splice).** Two fiber elements that agree on the two crossing bonds can be combined: the
labels of the second on the bonds touching `Y` and of the first elsewhere form a fiber element. -/
theorem lemmaD_splice {E : Type*} [AddCommGroup E] {a b : V} {r : E} {Y : Finset V}
    {ℓ ℓ' : Bond M S} (hcut : ∀ e, Crosses Y e ↔ e = ℓ ∨ e = ℓ')
    (k₁ k₂ : FlowFiber M S a b E r) (h1 : k₁.1 ℓ = k₂.1 ℓ) (h2 : k₁.1 ℓ' = k₂.1 ℓ') :
    let k : Bond M S → E := fun e => if tl e ∈ Y ∨ hd e ∈ Y then k₂.1 e else k₁.1 e
    flow M S k a = -r ∧ flow M S k b = r ∧ ∀ v ∈ S, v ≠ a → v ≠ b → flow M S k v = 0 := by
  classical
  intro k
  have key : ∀ v, flow M S k v = if v ∈ Y then flow M S k₂.1 v else flow M S k₁.1 v := by
    intro v
    unfold flow
    split_ifs with hv
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases he : tl e = v ∨ hd e = v
      · have : tl e ∈ Y ∨ hd e ∈ Y := by rcases he with he | he <;> [left; right] <;> rw [he] <;> exact hv
        simp only [k, this, ite_true]
      · have h1' : tl e ≠ v := fun h => he (Or.inl h)
        have h2' : hd e ≠ v := fun h => he (Or.inr h)
        rw [incidence_eq]; simp [h1', h2']
    · refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases he : tl e = v ∨ hd e = v
      · by_cases hY : tl e ∈ Y ∨ hd e ∈ Y
        · have hc : Crosses Y e := by
            unfold Crosses
            rcases he with he | he <;> rcases hY with hY | hY
            · rw [he] at hY; exact absurd hY hv
            · exact Or.inr ⟨hY, by rw [he]; exact hv⟩
            · exact Or.inl ⟨hY, by rw [he]; exact hv⟩
            · rw [he] at hY; exact absurd hY hv
          have hk : k₂.1 e = k₁.1 e := by
            rcases (hcut e).mp hc with rfl | rfl
            · exact h1.symm
            · exact h2.symm
          simp only [k, hY, hk, ite_true]
        · simp only [k, hY, ite_false]
      · have h1' : tl e ≠ v := fun h => he (Or.inl h)
        have h2' : hd e ≠ v := fun h => he (Or.inr h)
        rw [incidence_eq]; simp [h1', h2']
  refine ⟨?_, ?_, ?_⟩
  · rw [key]; split_ifs <;> [exact k₂.2.1; exact k₁.2.1]
  · rw [key]; split_ifs <;> [exact k₂.2.2.1; exact k₁.2.2.1]
  · intro v hv ha hb
    rw [key]; split_ifs <;> [exact k₂.2.2.2 v hv ha hb; exact k₁.2.2.2 v hv ha hb]

/-- **Lemma D, the `δ`-system.** At a balanced atom the conservation law is invariant under adding one vector to all
labels. -/
theorem flow_add_const {E : Type*} [AddCommGroup E] (k : Bond M S → E) (c : E) {v : V}
    (hbal : (∑ e : Bond M S, incidence M v e.1) = 0) :
    flow M S (fun e => k e + c) v = flow M S k v := by
  unfold flow
  simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hbal, zero_smul, add_zero]

/-- The energy under a constant shift of all labels. -/
theorem energy_add_const {d : ℕ} (k : Bond M S → Mom d) (c : Mom d) (v : V) :
    energy M S (fun e => k e + c) v =
      energy M S k v - 2 * inner ℝ c (flow M S k v) - ((∑ e : Bond M S, incidence M v e.1 : ℤ) : ℝ) * ‖c‖ ^ 2 := by
  unfold energy flow
  simp only [inner_sum, Int.cast_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, norm_add_sq_real, real_inner_comm (k e) c]
  ring

/-- **Lemma D, κ-freeness of the quadratic forms.** At a balanced atom with conservation the energy is invariant under
adding one vector to all labels. -/
theorem energy_add_const_of_balanced {d : ℕ} (k : Bond M S → Mom d) (c : Mom d) {v : V}
    (hbal : (∑ e : Bond M S, incidence M v e.1) = 0) (hflow : flow M S k v = 0) :
    energy M S (fun e => k e + c) v = energy M S k v := by
  rw [energy_add_const, hbal, hflow]; simp

/-- The balanced-atom phase identity: with `o₁ + o₂ = i₁ + i₂`,
`|i₁|² + |i₂|² − |o₁|² − |o₂|² = −2⟨o₁ − i₁, o₁ − i₂⟩`. -/
theorem phase_identity {d : ℕ} (o₁ o₂ i₁ i₂ : Mom d) (h : o₁ + o₂ = i₁ + i₂) :
    ‖i₁‖ ^ 2 + ‖i₂‖ ^ 2 - ‖o₁‖ ^ 2 - ‖o₂‖ ^ 2 = -2 * inner ℝ (o₁ - i₁) (o₁ - i₂) := by
  have ho₂ : o₂ = i₁ + i₂ - o₁ := by rw [← h]; abel
  subst ho₂
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_comm i₁ i₂, real_inner_comm i₁ o₁, real_inner_comm i₂ o₁]
  ring

/-- The star: one atom with two outgoing (`0, 1`) and two incoming (`2, 3`) stubs. -/
abbrev starGraph : LocalGraph where
  nA := 1
  nB := 4
  src := ![some 0, some 0, none, none]
  dst := ![none, none, some 0, some 0]

/-- **Lemma D, the quadratic form at a degree-4 atom.** If the bonds of `S` at `v` are exactly two outgoing
`o₁, o₂` and two incoming `i₁, i₂` (a star embedding) and the flow at `v` vanishes, then the energy at `v` is
`−2⟨k_{o₁} − k_{i₁}, k_{o₁} − k_{i₂}⟩`. -/
theorem energy_star {d : ℕ} (φ : LocEmb starGraph M S) (k : Bond M S → Mom d)
    (hflow : flow M S k (φ.atom 0) = 0) :
    energy M S k (φ.atom 0) =
      -2 * inner ℝ (k (φ.bond 0) - k (φ.bond 2)) (k (φ.bond 0) - k (φ.bond 3)) := by
  rw [φ.flow_transfer] at hflow
  rw [φ.energy_transfer]
  have e0 : starGraph.inc 0 0 = 1 := by decide
  have e1 : starGraph.inc 0 1 = 1 := by decide
  have e2 : starGraph.inc 0 2 = -1 := by decide
  have e3 : starGraph.inc 0 3 = -1 := by decide
  rw [Fin.sum_univ_four, e0, e1, e2, e3] at hflow ⊢
  have hc : k (φ.bond 0) + k (φ.bond 1) = k (φ.bond 2) + k (φ.bond 3) := by
    rw [← sub_eq_zero, ← hflow]; simp only [one_smul, neg_smul]; abel
  rw [← phase_identity _ _ _ _ hc]
  push_cast
  ring

end WaveTurbulence.TVine.Chart
