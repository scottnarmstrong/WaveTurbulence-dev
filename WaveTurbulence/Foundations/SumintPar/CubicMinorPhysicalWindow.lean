/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.CubicGlobalIntegral
public import WaveTurbulence.Foundations.SumintPar.NonnegativeTimeRescale
public import WaveTurbulence.Foundations.SumintPar.SignedRescale

/-!
# The physical-time large-region normal bound

Rescaling both quadratic times keeps the full cubic Weyl reserve.
The third-time modulations remain unrestricted because they are fixed
throughout each two-time inner integral.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal
open scoped Classical

namespace WaveTurbulence.SumintPar

/-- The normal large-region mass in physical source times, before the linear branch is chosen. -/
theorem exists_cubic_minor_physical_window_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C R : ℝ, 0 ≤ C ∧ 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (sel : Bool) (a b p : Mom d) (ξ ζ ω : ℝ → Mom d) (c v w ε₀ ε₁ : ℝ), ε₀ = 1 ∨ ε₀ = -1 → ε₁ = 1 ∨ ε₁ = -1 → 0 < c → v ≤ w →
      (∫⁻ t in Icc v w, ∫⁻ s : ℝ, ∫⁻ s' : ℝ,
        if L ≤ max |c*(s-t)| |c*(s'-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) ∧ |c*(s'-t)| ≤ T₀*L^(2*γ) then
          ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0) ≤
        ENNReal.ofReal ((w-v)*c⁻¹*c⁻¹*C*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L) := by
  obtain ⟨C,R,hbound⟩ := WeylSums.quadExpSum3_bound d hd γ hγ T₀ hT₀
  refine ⟨max C 0,max R 2,le_max_right _ _,le_max_right _ _,?_⟩
  intro L hL sel a b p ξ ζ ω c v w ε₀ ε₁ h₀ h₁ hc hvw
  have hL2 : 2 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := by linarith only [hL2]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith only [hL2])
  let T := WeylSums.timeSquareWindow L (T₀*L^(2*γ))
  have hT : MeasurableSet T := WeylSums.measurableSet_timeSquareWindow _ _
  let B := max C 0*L^(3*(d:ℝ)+γ-2*min γ (1-γ))*Real.log L
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (t : ℝ) :
      (∫⁻ s : ℝ, ∫⁻ s' : ℝ,
        if L ≤ max |c*(s-t)| |c*(s'-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) ∧ |c*(s'-t)| ≤ T₀*L^(2*γ) then
          ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0) ≤
        ENNReal.ofReal c⁻¹*ENNReal.ofReal c⁻¹*ENNReal.ofReal B := by
    let F := fun z : ℝ × ℝ => ‖WeylSums.cubicLatticeSum L z.1 z.2 sel a b p (ξ t) (ζ t) (ω t)‖
    have hF : Continuous F := (WeylSums.continuous_cubicLatticeSum hLp sel a b p (ξ t) (ζ t) (ω t)).norm
    have hi : IntegrableOn F T := hF.integrableOn_Icc.mono_set
      (show T ⊆ Icc (-(T₀*L^(2*γ)),-(T₀*L^(2*γ))) (T₀*L^(2*γ),T₀*L^(2*γ)) from
        fun z hz => ⟨⟨(abs_le.mp hz.2.1).1,(abs_le.mp hz.2.2).1⟩,
          ⟨(abs_le.mp hz.2.1).2,(abs_le.mp hz.2.2).2⟩⟩)
    have hn : (∫⁻ z in T, ENNReal.ofReal (F z)) ≤ ENNReal.ofReal B := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun z => norm_nonneg _))]
      apply ENNReal.ofReal_le_ofReal
      exact (hbound L ((le_max_left _ _).trans hL) sel a b p (ξ t) (ζ t) (ω t)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hLp.le _)) hlog)
    let f := T.indicator (fun z => ENNReal.ofReal (F z))
    have hf : Measurable f := (ENNReal.measurable_ofReal.comp hF.measurable).indicator hT
    have habs₀ : |ε₀| = 1 := by rcases h₀ with rfl | rfl <;> simp
    have habs₁ : |ε₁| = 1 := by rcases h₁ with rfl | rfl <;> simp
    have he (s s' : ℝ) :
        (if L ≤ max |c*(s-t)| |c*(s'-t)| ∧ |c*(s-t)| ≤ T₀*L^(2*γ) ∧ |c*(s'-t)| ≤ T₀*L^(2*γ) then
          ‖WeylSums.cubicLatticeSum L (ε₀*(c*(s-t))) (ε₁*(c*(s'-t))) sel a b p (ξ t) (ζ t) (ω t)‖ₑ else 0) =
        f (ε₀*(c*(s-t)),ε₁*(c*(s'-t))) := by
      simp only [f,T,F,indicator_apply,WeylSums.timeSquareWindow,mem_ofPred_eq,ofReal_norm,
        abs_mul,habs₀,habs₁,one_mul]
    simp_rw [he]
    rw [lintegral_comp_affine_two_signed f hf hc t h₀ h₁,lintegral_indicator hT]
    exact mul_le_mul' le_rfl hn
  calc
    _ ≤ ∫⁻ _t in Icc v w, ENNReal.ofReal c⁻¹*ENNReal.ofReal c⁻¹*ENNReal.ofReal B := lintegral_mono hb
    _ = _ := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,
        ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
        ← ENNReal.ofReal_mul (mul_nonneg (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hc.le)),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (inv_nonneg.mpr hc.le) (inv_nonneg.mpr hc.le)) hB)]
      congr 1
      dsimp [B]
      ring

end WaveTurbulence.SumintPar
