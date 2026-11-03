/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LayerLink

/-!
# Integer-layer separation

TARGET (incohproof11), (incohproof15): distinct integer layers have a fixed
separating integer. The orientation is fixed on the whole link box.
-/

public section

namespace WaveTurbulence.Incoh

/-- The separating integer is shared by every point in an incoherent link box. -/
theorem exists_separating_layer {d : ℕ} (Q : LayerLink d) (hQ : Q.IsIncoherent) :
    ∃ q : ℤ,
      (∀ t ∈ linkBox Q, t 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t 1) ∨
      (∀ t ∈ linkBox Q, t 1 ≤ (q : ℝ) ∧ (q : ℝ) ≤ t 0) := by
  have hne : Q.leftLayer ≠ Q.rightLayer := hQ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨Q.rightLayer, Or.inl ?_⟩
    intro t ht
    have hcast : (Q.leftLayer : ℝ) + 1 ≤ Q.rightLayer := by
      have hi : Q.leftLayer + 1 ≤ Q.rightLayer := by omega
      exact_mod_cast hi
    exact ⟨(ht.2 0).trans hcast, ht.1 1⟩
  · refine ⟨Q.leftLayer, Or.inr ?_⟩
    intro t ht
    have hcast : (Q.rightLayer : ℝ) + 1 ≤ Q.leftLayer := by
      have hi : Q.rightLayer + 1 ≤ Q.leftLayer := by omega
      exact_mod_cast hi
    exact ⟨(ht.2 1).trans hcast, ht.1 0⟩

/-- The source's distance-to-separator bound, in either orientation. -/
theorem abs_sub_separator_le {x y q : ℝ} (h : (x ≤ q ∧ q ≤ y) ∨ (y ≤ q ∧ q ≤ x)) :
    |x - q| ≤ |x - y| := by
  rcases h with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonpos (sub_nonpos.mpr (h.1.trans h.2))]
    linarith [h.2]
  · rw [abs_of_nonneg (sub_nonneg.mpr h.2), abs_of_nonneg (sub_nonneg.mpr (h.1.trans h.2))]
    linarith [h.1]

end WaveTurbulence.Incoh
