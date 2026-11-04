/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearGlobalIntegral

/-!
# Retained small- and large-region bilinear bounds

The ordinary full-window estimate discards the large-region reserve.
Bad and incoherent blocks retain it here, alongside the small-region
first moment. This separates the two distinct gain mechanisms.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- The small first moment and the full large-region gain hold simultaneously
with constants independent of all spatial shifts and modulations. -/
theorem exists_bilinear_split_integral_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d,
      (∫ s in {s : ℝ | |s| ≤ L}, (1+|s|)*‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) ≤
        Cs*L^(2*d) ∧
      (∫ s in {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀*L^(2*γ)},
        ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖) ≤
          Cm*L^(2*(d:ℝ)-2*((d:ℝ)-1)*(1-γ)+η) := by
  obtain ⟨Cs,hCs,hs⟩ := exists_bilinear_small_integral_bound d hd
  obtain ⟨Cm,R,hm⟩ := WeylSums.quadExpSum2_bound d hd γ hγ η hη T₀ hT₀
  refine ⟨Cs,max Cm 0,max R 2,hCs,le_max_right _ _,le_max_right _ _,?_⟩
  intro L hL a b ξ ζ
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  refine ⟨hs (by linarith) a b ξ ζ, ?_⟩
  exact (hm L ((le_max_left _ _).trans hL) a b ξ ζ).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by linarith : 0 ≤ L) _))

end WaveTurbulence.Sumint
