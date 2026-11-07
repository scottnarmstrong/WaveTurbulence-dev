/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib
import Mathlib.Tactic

/-!
# Time gaps behind bad-block and incoherence gains

The enlarged-interval estimate keeps an explicit `2h` error. It is the
source replacement for the disjoint-unit-interval estimate after the
`L^{-β}` localization in Step 3.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.SumintPar

/-- The case (a) ordering bounds the distance to the middle time by the pair gap. -/
theorem abs_sub_middle_le {s t₀ t₁ : ℝ}
    (h : (s < t₀ ∧ t₀ < t₁) ∨ (t₁ < t₀ ∧ t₀ < s)) :
    |t₁ - t₀| ≤ |t₁ - s| := by
  rcases h with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ t₁ - t₀),
      abs_of_nonneg (by linarith : 0 ≤ t₁ - s)]
    linarith
  · rw [abs_of_nonpos (by linarith : t₁ - t₀ ≤ 0),
      abs_of_nonpos (by linarith : t₁ - s ≤ 0)]
    linarith

/-- Distinct translated and enlarged unit intervals force proximity to an endpoint. -/
theorem enlarged_unit_gap_endpoint {q p : ℕ} (hqp : q ≠ p) {h a u v : ℝ} (hh : 0 ≤ h)
    (hu : (q : ℝ) - a - h ≤ u ∧ u ≤ (q : ℝ) + 1 - a + h)
    (hv : (p : ℝ) - a - h ≤ v ∧ v ≤ (p : ℝ) + 1 - a + h) :
    ∃ e : ℝ, (e = (q : ℝ) - a ∨ e = (q : ℝ) + 1 - a) ∧
      |u - e| ≤ 2 * h + |u - v| := by
  have hab := abs_le.mp (le_refl |u - v|)
  rcases lt_or_gt_of_ne hqp with hlt | hgt
  · have hp : (q : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hlt
    refine ⟨(q : ℝ) + 1 - a, Or.inr rfl, abs_le.mpr ?_⟩
    constructor <;> linarith only [hu.2, hv.1, hp, hh, hab.1, hab.2]
  · have hp : (p : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt hgt
    refine ⟨(q : ℝ) - a, Or.inl rfl, abs_le.mpr ?_⟩
    constructor <;> linarith only [hu.1, hv.2, hp, hh, hab.1, hab.2]

end WaveTurbulence.SumintPar
