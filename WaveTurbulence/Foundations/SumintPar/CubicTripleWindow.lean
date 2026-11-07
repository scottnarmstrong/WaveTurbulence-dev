/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CubicTimeWindow

/-!
# Integrating the third time of the normal factor

The three linear momentum modulations may depend on the third time.
Uniformity in the landed estimate permits their dependence to be kept
until that last time is integrated.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set

namespace WaveTurbulence.SumintPar

/-- Full ordinary normal-factor cancellation on a rectangular time window. -/
theorem exists_cubic_triple_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0 : ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ Cs Cm L₀ : ℝ, 0 ≤ Cs ∧ 0 ≤ Cm ∧ 2 ≤ L₀ ∧
      ∀ L ≥ L₀, ∀ (sel : Bool) (p q r : Mom d) (ξ ζ ω : ℝ → Mom d),
      ∀ c a b l u v w ε₀ ε₁ : ℝ, ε₀ = 1 ∨ ε₀ = -1 → ε₁ = 1 ∨ ε₁ = -1 → 0 < c → a ≤ b → l ≤ u → v ≤ w →
      (∀ t ∈ Icc v w,
        (-(T₀*L^(2*γ)) ≤ c*(a-t) ∧ c*(b-t) ≤ T₀*L^(2*γ)) ∧
        (-(T₀*L^(2*γ)) ≤ c*(l-t) ∧ c*(u-t) ≤ T₀*L^(2*γ))) →
      (∫ t in Icc v w, ∫ s in Icc a b, ∫ s' in Icc l u,
        ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel p q r (ξ t) (ζ t) (ω t)‖) ≤
      (w-v)*c⁻¹*c⁻¹ *
        (Cs*L^(3*d)+Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L) := by
  obtain ⟨Cs,Cm,L₀,hCs,hCm,hL₀,hbound⟩ :=
    exists_cubic_affine_window_bound d hd γ hγ T₀ hT₀
  refine ⟨Cs,Cm,L₀,hCs,hCm,hL₀,?_⟩
  intro L hL sel p q r ξ ζ ω c a b l u v w ε₀ ε₁ h₀ h₁ hc hab hlu hvw hwin
  let B := c⁻¹*c⁻¹ *
    (Cs*L^(3*d)+Cm*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L)
  have hb : ∀ᵐ t ∂volume.restrict (Icc v w),
      (∫ s in Icc a b, ∫ s' in Icc l u,
        ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel p q r (ξ t) (ζ t) (ω t)‖) ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hbound L hL sel p q r (ξ t) (ζ t) (ω t) c a b l u t ε₀ ε₁ h₀ h₁ hc hab hlu
      (hwin t ht).1.1 (hwin t ht).1.2 (hwin t ht).2.1 (hwin t ht).2.2
  calc
    _ ≤ ∫ _t in Icc v w, B := integral_mono_of_nonneg
      (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => norm_nonneg _))))
      (integrable_const B) hb
    _ = _ := by
      rw [integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hvw),smul_eq_mul]
      dsimp [B]
      ring

end WaveTurbulence.SumintPar
