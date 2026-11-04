/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.TimeBoxCoordinates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rectangular root-box integrals as double interval integrals

TARGET (incohproof17)–(incohproof19). Closed and half-open endpoints
have the same Lebesgue integral; coordinate transport and Fubini give the
literal oriented interval formula on the ordered root box.
-/

public section
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Incoh

/-- Transport the literal two-time box integral to a product of scalar intervals. -/
theorem setIntegral_twoTimeBox (a b c d : ℝ) (f : ℝ × ℝ → ℂ) :
    (∫ t : Fin 2 → ℝ in Icc ![a, c] ![b, d], f (t 0, t 1)) =
      ∫ z : ℝ × ℝ in Icc a b ×ˢ Icc c d, f z := by
  rw [← preimage_finTwoArrow_Icc]
  exact (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding f _

/-- An integrable actual root density has the literal double interval formula on every ordered box. -/
theorem integral_twoTimeBox_eq_doubleInterval {F : (Fin 2 → ℝ) → ℂ} (hF : Integrable F)
    (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ t in Icc ![a, c] ![b, d], F t) =
      ∫ u in a..b, ∫ v in c..d, F ![u, v] := by
  let G : ℝ × ℝ → ℂ := fun z => F (MeasurableEquiv.finTwoArrow.symm z)
  have hG : Integrable G :=
    ((volume_preserving_finTwoArrow ℝ).symm.integrable_comp_emb
      MeasurableEquiv.finTwoArrow.symm.measurableEmbedding).mpr hF
  have heq (t : Fin 2 → ℝ) : G (t 0, t 1) = F t := by
    change F (MeasurableEquiv.finTwoArrow.symm (MeasurableEquiv.finTwoArrow t)) = _
    rw [MeasurableEquiv.symm_apply_apply]
  simp_rw [← heq]
  rw [setIntegral_twoTimeBox]
  change (∫ z in Icc a b ×ˢ Icc c d, G z ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
  rw [setIntegral_prod G hG.integrableOn]
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hcd, ← integral_Icc_eq_integral_Ioc]
  rfl

end WaveTurbulence.Incoh
