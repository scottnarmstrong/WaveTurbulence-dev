/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.TimeDerivatives
public import WaveTurbulence.Foundations.Fourier.TimeIntegralOperators
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# Compact smooth functions controlled by their mixed derivative

TARGET A.3 is used in the smooth compactly supported class, as ruled by
the owner. Two applications of the one-dimensional fundamental theorem
control the amplitude uniformly by the global mixed derivative `L¹` norm.
No support radius enters the bound.
-/

public section

open MeasureTheory Set Function
open scoped ContDiff ENNReal

namespace WaveTurbulence.Fourier

/-- The fundamental theorem on a coordinate line, with the frozen partial derivative. -/
theorem enorm_le_lintegral_partialDeriv {r : ℕ} {F : (Fin r → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (j : Fin r) (x : Fin r → ℝ) :
    ‖F x‖ₑ ≤ ∫⁻ u : ℝ, ‖WaveTurbulence.partialDeriv j F (update x j u)‖ₑ := by
  have hs : HasCompactSupport (F ∘ update x j) :=
    hc.comp_isClosedEmbedding (isClosedEmbedding_update x j)
  have hd : ContDiff ℝ 1 (F ∘ update x j) :=
    (hF.of_le (by simp)).comp (contDiff_update 1 x j)
  have h := HasCompactSupport.enorm_le_lintegral_Ici_deriv hd hs (x j)
  simp only [comp_apply, update_eq_self] at h
  apply h.trans
  calc
    _ ≤ ∫⁻ u : ℝ, ‖deriv (F ∘ update x j) u‖ₑ :=
      setLIntegral_le_lintegral _ _
    _ = _ := by
      apply lintegral_congr
      intro u
      congr 1
      rw [fderiv_comp_deriv u (hF.differentiable (by simp) (update x j u))
        (WaveTurbulence.hasDerivAt_update x j u).differentiableAt,
        (WaveTurbulence.hasDerivAt_update x j u).deriv]
      exact (WaveTurbulence.partialDeriv_eq_fderiv
        (hF.differentiable (by simp) (update x j u)) j).symm


/-- The mixed derivative controls the amplitude globally, with constant one. -/
theorem enorm_le_lintegral_mixedTimePartial {F : (Fin 2 → ℝ) → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (x : Fin 2 → ℝ) :
    ‖F x‖ₑ ≤ ∫⁻ y, ‖mixedTimePartial F y‖ₑ := by
  have hd := WaveTurbulence.contDiff_infty_partialDeriv hF 1
  have hs := hasCompactSupport_partialDeriv (hF.differentiable (by simp)) hc 1
  calc
    _ ≤ ∫⁻ v : ℝ, ‖WaveTurbulence.partialDeriv 1 F (update x 1 v)‖ₑ :=
      enorm_le_lintegral_partialDeriv hF hc 1 x
    _ ≤ ∫⁻ v : ℝ, ∫⁻ u : ℝ, ‖mixedTimePartial F ![u, v]‖ₑ := by
      apply lintegral_mono
      intro v
      calc
        _ ≤ ∫⁻ u : ℝ, ‖WaveTurbulence.partialDeriv 0 (WaveTurbulence.partialDeriv 1 F)
            (update (update x 1 v) 0 u)‖ₑ :=
          enorm_le_lintegral_partialDeriv hd hs 0 (update x 1 v)
        _ = _ := by
          apply lintegral_congr
          intro u
          have he : update (update x 1 v) 0 u = ![u, v] := by
            ext j
            fin_cases j <;> simp
          rw [he]
          rfl
    _ = _ := by
      have hm := volume_preserving_finTwoArrow ℝ
      have hmixed : Continuous (mixedTimePartial F) :=
        (WaveTurbulence.contDiff_infty_partialDeriv hd 0).continuous
      have hmeas : Measurable (fun z : ℝ × ℝ => ‖mixedTimePartial F ![z.1, z.2]‖ₑ) :=
        (hmixed.comp (by fun_prop)).measurable.enorm
      calc
        _ = ∫⁻ z : ℝ × ℝ, ‖mixedTimePartial F ![z.1, z.2]‖ₑ :=
          (lintegral_prod_symm _ hmeas.aemeasurable).symm
        _ = _ := by
          calc
            _ = ∫⁻ z : ℝ × ℝ, ‖mixedTimePartial F (MeasurableEquiv.finTwoArrow.symm z)‖ₑ := by
              apply lintegral_congr
              intro z
              have he : ![z.1, z.2] = MeasurableEquiv.finTwoArrow.symm z := by
                ext i
                fin_cases i <;> rfl
              rw [he]
            _ = _ := hm.symm.lintegral_comp_emb
              MeasurableEquiv.finTwoArrow.symm.measurableEmbedding (fun y => ‖mixedTimePartial F y‖ₑ)

end WaveTurbulence.Fourier
