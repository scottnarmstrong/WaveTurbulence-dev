/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CompactParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Smooth parameter-dependent oriented interval integrals

An affine change of variables reduces every moving interval to `[0,1]`.
The resulting fixed compact integral preserves smoothness even when the
endpoints coincide or reverse order.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Fourier

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Smoothness of an oriented interval integral with smooth parameters and endpoints. -/
theorem contDiff_intervalIntegral {G : E × ℝ → H} {a b : E → ℝ}
    (hG : ContDiff ℝ ∞ G) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun w => ∫ u in a w..b w, G (w, u)) := by
  let F : E × ℝ → H := fun p => G (p.1, a p.1 + (b p.1 - a p.1) * p.2)
  have hF : ContDiff ℝ ∞ F := hG.comp
    (contDiff_fst.prodMk ((ha.comp contDiff_fst).add
      (((hb.sub ha).comp contDiff_fst).mul contDiff_snd)))
  have hI : ContDiff ℝ ∞ (fun w => ∫ u in (0 : ℝ)..1, F (w, u)) := by
    have h := compact_param_integral_contDiff_infty (μ := volume) (Q := Icc (0 : ℝ) 1)
      isCompact_Icc hF
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc] using h
  have h := (hb.sub ha).smul hI
  convert h using 1
  funext w
  change (∫ u in a w..b w, G (w, u)) =
    (b w - a w) • ∫ u in (0 : ℝ)..1, G (w, a w + (b w - a w) * u)
  have he := intervalIntegral.smul_integral_comp_add_mul (fun u => G (w, u))
    (b w - a w) (a w) (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, add_zero, mul_one] at he
  rw [show a w + (b w - a w) = b w by ring] at he
  exact he.symm

end WaveTurbulence.Fourier
