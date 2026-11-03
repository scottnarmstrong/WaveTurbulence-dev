/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Resonant.LocalizedAmplitude

/-!
# Fixed bounds for smooth spatial cutoffs

Every continuously differentiable compactly supported spatial cutoff has a
bounded range, a global Lipschitz constant, and a support radius. All witnesses
are chosen before any localization center or scale, preserving uniformity.
-/

public section

open MeasureTheory Set
open scoped NNReal ContDiff

namespace WaveTurbulence.Resonant

variable {d : ℕ}

/-- Compact support and `C¹` regularity give a global Lipschitz constant. -/
theorem exists_lipschitzWith_of_contDiff_compact {f : Mom d → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0, LipschitzWith K f := by
  have hfd := hf.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  obtain ⟨C, hC⟩ := hfd.bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num))
  intro x
  change ‖fderiv ℝ f x‖ ≤ max C 0
  exact (hC x).trans (le_max_left _ _)

/-- A nonnegative range bound for a fixed continuous compact cutoff. -/
theorem exists_nnreal_bound_cutoff {f : Mom d → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ∃ B : ℝ≥0, ∀ x, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun x => ?_⟩
  have hx : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
  exact hx.trans (le_max_left _ _)

/-- A support radius at least one, without any dependence on later centers or scales. -/
theorem exists_support_radius_cutoff {f : Mom d → ℝ} (hc : HasCompactSupport f) :
    ∃ r : ℝ, 1 ≤ r ∧ ∀ z, r < ‖z‖ → f z = 0 := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.exists_norm_le
  refine ⟨max R 1, le_max_right _ _, fun z hz => ?_⟩
  by_contra hne
  have hm : z ∈ tsupport f := subset_tsupport f hne
  have hn := hR z hm
  exact (not_le_of_gt hz) (hn.trans (le_max_left _ _))

end WaveTurbulence.Resonant
