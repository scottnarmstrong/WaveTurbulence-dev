/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.BilinearGlobalIntegral
public import WaveTurbulence.Foundations.Sumint.WindowRescaleGeneral

/-!
# Bilinear factors on enlarged source time intervals

The full symmetric-window estimate applies to every affine image of a
closed interval contained in that window. This retains uniformity in
all spatial Fourier modulations before the outer time is integrated.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- Uniform bilinear cancellation on all source subwindows at positive scale. -/
theorem exists_bilinear_affine_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηγ : η ≤ 2*((d:ℝ)-1)*(1-γ)) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C L₀ : ℝ, 0 ≤ C ∧ 2 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ a b ξ ζ : Mom d,
      ∀ c l u t : ℝ, 0 < c → l ≤ u →
      -(T₀*L^(2*γ)) ≤ c*(l-t) → c*(u-t) ≤ T₀*L^(2*γ) →
      (∫ s in Icc l u, ‖WeylSums.bilinearLatticeSum L (c*(s-t)) a b ξ ζ‖) ≤
        c⁻¹ * C * L^(2*d) := by
  obtain ⟨C,L₀,hC,hL₀,hbound⟩ :=
    exists_bilinear_global_integral_bound d hd γ hγ η hη hηγ T₀ hT₀
  refine ⟨C,L₀,hC,hL₀,?_⟩
  intro L hL a b ξ ζ c l u t hc hlu hlo hhi
  obtain ⟨hi,hb⟩ := hbound L hL a b ξ ζ
  rw [abs_window_eq_Icc] at hi hb
  calc
    _ ≤ c⁻¹ * ∫ s in Icc (-(T₀*L^(2*γ))) (T₀*L^(2*γ)),
        ‖WeylSums.bilinearLatticeSum L s a b ξ ζ‖ :=
      integral_Icc_affine_le_symmetric _ hc hlu t hi (fun _ => norm_nonneg _) hlo hhi
    _ ≤ c⁻¹ * (C*L^(2*d)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    _ = _ := by ring

end WaveTurbulence.Sumint
