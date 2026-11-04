/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicGlobalIntegral
public import WaveTurbulence.Foundations.Sumint.WindowRescaleTwo

/-!
# The cubic estimate on enlarged source time rectangles

Both stationary and Weyl contributions are kept separately. Their
relative exponents decide which linear branch is paired with a normal
factor in TARGET sumint.
-/

public section

open MeasureTheory Set

namespace WaveTurbulence.Sumint

/-- Cubic cancellation on any affine rectangle contained in the landed square. -/
theorem exists_cubic_affine_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ (sel : Bool) (p q r ξ ζ ω : Mom d),
      ∀ c a b l u t : ℝ, 0 < c → a ≤ b → l ≤ u →
      -(T₀*L^(2*γ)) ≤ c*(a-t) → c*(b-t) ≤ T₀*L^(2*γ) →
      -(T₀*L^(2*γ)) ≤ c*(l-t) → c*(u-t) ≤ T₀*L^(2*γ) →
      (∫ s in Icc a b, ∫ s' in Icc l u,
        ‖WeylSums.cubicLatticeSum L (c*(s-t)) (c*(s'-t)) sel p q r ξ ζ ω‖) ≤
      c⁻¹*c⁻¹ * (Cs*L^(3*d)+Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_cubic_global_integral_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL sel p q r ξ ζ ω c a b l u t hc hab hlu ha hb hl hu
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (hL₀.trans hL)
  have hcont := (WeylSums.continuous_cubicLatticeSum hLp sel p q r ξ ζ ω).norm
  have hbnd := (hbound L hL sel p q r ξ ζ ω).2
  exact (integral_Icc_affine_two_le_square _ hcont (fun _ => norm_nonneg _)
    hc hab hlu t ha hb hl hu).trans
      (mul_le_mul_of_nonneg_left hbnd (by positivity))

end WaveTurbulence.Sumint
