/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicYoung
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The real-valued three-factor Young inequality -/

public section
open MeasureTheory
namespace WaveTurbulence.WeylSums

/-- Real-valued Young inequality, including the integrability conclusion
needed when it is used as a lattice-sum majorant. -/
theorem integral_triple_add_le (f g h : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hfi : Integrable (fun x => f x^((3 : ℝ)/2)))
    (hgi : Integrable (fun x => g x^((3 : ℝ)/2)))
    (hhi : Integrable (fun x => h x^((3 : ℝ)/2))) :
    Integrable (fun xy : ℝ × ℝ => f xy.1*g xy.2*h (xy.1+xy.2)) ∧
    (∫ xy : ℝ × ℝ, f xy.1*g xy.2*h (xy.1+xy.2)) ≤
      (∫ x, f x^((3 : ℝ)/2))^((2 : ℝ)/3)*
      (∫ y, g y^((3 : ℝ)/2))^((2 : ℝ)/3)*
      (∫ z, h z^((3 : ℝ)/2))^((2 : ℝ)/3) := by
  let v (xy : ℝ × ℝ) := f xy.1*g xy.2*h (xy.1+xy.2)
  let R := (∫ x, f x^((3 : ℝ)/2))^((2 : ℝ)/3)*
    (∫ y, g y^((3 : ℝ)/2))^((2 : ℝ)/3)*
    (∫ z, h z^((3 : ℝ)/2))^((2 : ℝ)/3)
  have hIf : 0 ≤ ∫ x, f x^((3 : ℝ)/2) := integral_nonneg (fun x => Real.rpow_nonneg (hfn x) _)
  have hIg : 0 ≤ ∫ x, g x^((3 : ℝ)/2) := integral_nonneg (fun x => Real.rpow_nonneg (hgn x) _)
  have hIh : 0 ≤ ∫ x, h x^((3 : ℝ)/2) := integral_nonneg (fun x => Real.rpow_nonneg (hhn x) _)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hvn (xy : ℝ × ℝ) : 0 ≤ v xy := mul_nonneg (mul_nonneg (hfn _) (hgn _)) (hhn _)
  have hvm : Measurable v := (hf.comp measurable_fst |>.mul (hg.comp measurable_snd)).mul
    (hh.comp (measurable_fst.add measurable_snd))
  have hmoment (u : ℝ → ℝ) (hn : ∀ x, 0 ≤ u x)
      (hi : Integrable (fun x => u x^((3 : ℝ)/2))) :
      (∫⁻ x, (ENNReal.ofReal (u x))^((3 : ℝ)/2)) =
        ENNReal.ofReal (∫ x, u x^((3 : ℝ)/2)) := by
    simp_rw [ENNReal.ofReal_rpow_of_nonneg (hn _) (by norm_num : (0 : ℝ) ≤ 3/2)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hn x) _))).symm
  have hy := lintegral_triple_add_le (fun x => ENNReal.ofReal (f x))
    (fun x => ENNReal.ofReal (g x)) (fun x => ENNReal.ofReal (h x))
    hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
  have hl : (∫⁻ xy, ENNReal.ofReal (v xy)) ≤ ENNReal.ofReal R := by
    rw [hmoment f hfn hfi,hmoment g hgn hgi,hmoment h hhn hhi] at hy
    have hRex : ENNReal.ofReal R =
        ENNReal.ofReal (∫ x, f x^((3 : ℝ)/2))^((2 : ℝ)/3)*
        ENNReal.ofReal (∫ x, g x^((3 : ℝ)/2))^((2 : ℝ)/3)*
        ENNReal.ofReal (∫ x, h x^((3 : ℝ)/2))^((2 : ℝ)/3) := by
      dsimp [R]
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hIf _) (Real.rpow_nonneg hIg _)),
        ENNReal.ofReal_mul (Real.rpow_nonneg hIf _),
        ← ENNReal.ofReal_rpow_of_nonneg hIf (by norm_num : (0 : ℝ) ≤ 2/3),
        ← ENNReal.ofReal_rpow_of_nonneg hIg (by norm_num : (0 : ℝ) ≤ 2/3),
        ← ENNReal.ofReal_rpow_of_nonneg hIh (by norm_num : (0 : ℝ) ≤ 2/3)]
    rw [hRex]
    convert hy using 1
    apply lintegral_congr
    intro xy
    dsimp [v]
    rw [ENNReal.ofReal_mul (mul_nonneg (hfn _) (hgn _)), ENNReal.ofReal_mul (hfn _)]
  have hvi : Integrable v := ⟨hvm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hvn)).mpr
      (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hvi,?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hR).mp
  rw [ofReal_integral_eq_lintegral_ofReal hvi (Filter.Eventually.of_forall hvn)]
  exact hl

end WaveTurbulence.WeylSums
