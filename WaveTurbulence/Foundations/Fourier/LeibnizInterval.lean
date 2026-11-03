/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.SmoothIntervalIntegral
public import WaveTurbulence.Foundations.Fourier.ProductDerivative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Leibniz differentiation of oriented interval integrals

Joint smoothness, compact integration, and the endpoint fundamental theorem
separate parameter variation from the two moving boundary faces.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace WaveTurbulence.Fourier

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Parameter differentiation under an arbitrary fixed oriented interval. -/
theorem hasFDerivAt_fixed_interval {G : E × ℝ → H} (hG : ContDiff ℝ ∞ G)
    (w : E) (a b : ℝ) :
    HasFDerivAt (fun z => ∫ u in a..b, G (z, u))
      (∫ u in a..b, (fderiv ℝ G (w, u)).comp (ContinuousLinearMap.inl ℝ E ℝ)) w := by
  have hpos : ∀ c d : ℝ, c ≤ d →
      HasFDerivAt (fun z => ∫ u in c..d, G (z, u))
        (∫ u in c..d, (fderiv ℝ G (w, u)).comp (ContinuousLinearMap.inl ℝ E ℝ)) w := by
    intro c d hcd
    have h := compact_param_integral_hasFDerivAt (U := univ) isOpen_univ
      (μ := volume) (Q := Icc c d) isCompact_Icc
      (hG.of_le (by simp) : ContDiff ℝ 1 G).contDiffOn (mem_univ w)
    simpa only [intervalIntegral.integral_of_le hcd, integral_Icc_eq_integral_Ioc] using h
  rcases le_total a b with hab | hba
  · exact hpos a b hab
  · have h := (hpos b a hba).neg
    change HasFDerivAt (fun z => -(∫ u in b..a, G (z, u))) _ w at h
    simpa only [← intervalIntegral.integral_symm] using h

/-- Full Leibniz rule, in continuous-linear-map form. -/
theorem hasFDerivAt_intervalIntegral {G : E × ℝ → H} {a b : E → ℝ}
    (hG : ContDiff ℝ ∞ G) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (w : E) :
    HasFDerivAt (fun z => ∫ u in a z..b z, G (z, u))
      ((∫ u in a w..b w, (fderiv ℝ G (w, u)).comp (ContinuousLinearMap.inl ℝ E ℝ)) +
        (fderiv ℝ b w).smulRight (G (w, b w)) -
        (fderiv ℝ a w).smulRight (G (w, a w))) w := by
  let J : E × (ℝ × ℝ) → H := fun p => ∫ u in p.2.1..p.2.2, G (p.1, u)
  have hJs : ContDiff ℝ ∞ J := by
    apply contDiff_intervalIntegral (G := fun p : (E × (ℝ × ℝ)) × ℝ => G (p.1.1, p.2))
    · exact hG.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
    · exact contDiff_fst.comp contDiff_snd
    · exact contDiff_snd.comp contDiff_snd
  have hc : Continuous (fun u => G (w, u)) :=
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  have hA := hasFDerivAt_fixed_interval hG w (a w) (b w)
  have hB := intervalIntegral.integral_hasFDerivAt (hc.intervalIntegrable (a w) (b w))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt hc.continuousAt
  have hj := hasFDerivAt_of_product_slices (f := J)
    (hJs.differentiable (by simp) (w, (a w, b w))) hA hB
  have h := hj.comp w ((hasFDerivAt_id w).prodMk
    (((ha.differentiable (by simp) w).hasFDerivAt).prodMk
      ((hb.differentiable (by simp) w).hasFDerivAt)))
  convert h using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.fst, ContinuousLinearMap.snd]
    abel

end WaveTurbulence.Fourier
