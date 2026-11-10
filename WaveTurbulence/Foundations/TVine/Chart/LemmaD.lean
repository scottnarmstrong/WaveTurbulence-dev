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

end WaveTurbulence.TVine.Chart
