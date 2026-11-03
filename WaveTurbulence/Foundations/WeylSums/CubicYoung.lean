/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# The three-factor Young inequality in the cubic Weyl reduction

TARGET L1565–L1567. Hölder on the three pair products proves the inequality
directly; translation invariance computes their two-dimensional integrals.
-/

public section
open MeasureTheory Finset
open scoped ENNReal
namespace WaveTurbulence.WeylSums

private theorem pair_product_rpow (x y z : ℝ≥0∞) (r : ℝ) (hr : 0 ≤ r) :
    (x*y)^r * (y*z)^r * (z*x)^r = x^(2*r)*y^(2*r)*z^(2*r) := by
  rw [ENNReal.mul_rpow_of_nonneg x y hr, ENNReal.mul_rpow_of_nonneg y z hr,
    ENNReal.mul_rpow_of_nonneg z x hr]
  calc
    _ = (x^r*x^r)*(y^r*y^r)*(z^r*z^r) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg r r hr hr,
        ← ENNReal.rpow_add_of_nonneg r r hr hr,
        ← ENNReal.rpow_add_of_nonneg r r hr hr]
      simp only [two_mul]

/-- The nonnegative three-factor Young inequality for the addition kernel.
It includes infinite values and needs only measurability. -/
theorem lintegral_triple_add_le (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ xy : ℝ × ℝ, f xy.1*g xy.2*h (xy.1+xy.2)) ≤
      (∫⁻ x : ℝ, f x^((3 : ℝ)/2))^((2 : ℝ)/3) *
      (∫⁻ y : ℝ, g y^((3 : ℝ)/2))^((2 : ℝ)/3) *
      (∫⁻ z : ℝ, h z^((3 : ℝ)/2))^((2 : ℝ)/3) := by
  let F : ℝ → ℝ≥0∞ := fun x => f x^((3 : ℝ)/2)
  let G : ℝ → ℝ≥0∞ := fun x => g x^((3 : ℝ)/2)
  let H : ℝ → ℝ≥0∞ := fun x => h x^((3 : ℝ)/2)
  have hF : Measurable F := hf.pow_const _
  have hG : Measurable G := hg.pow_const _
  have hH : Measurable H := hh.pow_const _
  let P : Fin 3 → (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun xy => F xy.1*G xy.2, fun xy => G xy.2*H (xy.1+xy.2), fun xy => H (xy.1+xy.2)*F xy.1]
  have hP (i : Fin 3) : AEMeasurable (P i) volume := by
    fin_cases i
    · exact ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).aemeasurable
    · exact ((hG.comp measurable_snd).mul (hH.comp (measurable_fst.add measurable_snd))).aemeasurable
    · exact ((hH.comp (measurable_fst.add measurable_snd)).mul (hF.comp measurable_fst)).aemeasurable
  have hprod (xy : ℝ × ℝ) : (∏ i : Fin 3, (P i xy)^((1 : ℝ)/3)) = f xy.1*g xy.2*h (xy.1+xy.2) := by
    simp only [P, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    change (F xy.1*G xy.2)^((1 : ℝ)/3) * (G xy.2*H (xy.1+xy.2))^((1 : ℝ)/3) *
      (H (xy.1+xy.2)*F xy.1)^((1 : ℝ)/3) = _
    rw [pair_product_rpow _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1/3)]
    simp only [F,G,H, ← ENNReal.rpow_mul,
      show (3/2 : ℝ)*(2*(1/3)) = 1 by norm_num, ENNReal.rpow_one]
  have hI₀ : (∫⁻ xy : ℝ × ℝ, P 0 xy) = (∫⁻ x, F x)*(∫⁻ y, G y) :=
    lintegral_prod_mul hF.aemeasurable hG.aemeasurable
  have hI₁ : (∫⁻ xy : ℝ × ℝ, P 1 xy) = (∫⁻ y, G y)*(∫⁻ z, H z) := by
    change (∫⁻ xy : ℝ × ℝ, P 1 xy ∂((volume : Measure ℝ).prod volume)) = _
    rw [lintegral_prod_symm _ (hP 1)]
    change (∫⁻ y : ℝ, ∫⁻ x : ℝ, G y*H (x+y)) = _
    have hin (y : ℝ) : (∫⁻ x : ℝ, G y*H (x+y)) = G y*(∫⁻ z, H z) := by
      have hm : AEMeasurable (fun x : ℝ => H (x+y)) volume :=
        (hH.comp (measurable_id.add_const y)).aemeasurable
      rw [lintegral_const_mul'' (G y) hm,
        lintegral_add_right_eq_self H y]
    simp_rw [hin]
    exact lintegral_mul_const'' _ hG.aemeasurable
  have hI₂ : (∫⁻ xy : ℝ × ℝ, P 2 xy) = (∫⁻ z, H z)*(∫⁻ x, F x) := by
    change (∫⁻ xy : ℝ × ℝ, P 2 xy ∂((volume : Measure ℝ).prod volume)) = _
    rw [lintegral_prod _ (hP 2)]
    change (∫⁻ x : ℝ, ∫⁻ y : ℝ, H (x+y)*F x) = _
    have hin (x : ℝ) : (∫⁻ y : ℝ, H (x+y)*F x) = (∫⁻ z, H z)*F x := by
      have hm : AEMeasurable (fun y : ℝ => H (x+y)) volume :=
        (hH.comp (measurable_const.add measurable_id)).aemeasurable
      rw [lintegral_mul_const'' (F x) hm,
        lintegral_add_left_eq_self H x]
    simp_rw [hin]
    exact lintegral_const_mul'' _ hF.aemeasurable
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := (volume : Measure (ℝ × ℝ)))
    (univ : Finset (Fin 3)) (f := P) (fun i hi => hP i)
    (p := fun _ => (1 : ℝ)/3) (by norm_num) (fun i hi => by norm_num)
  simp_rw [hprod] at hholder
  simp only [Fin.prod_univ_three, hI₀,hI₁,hI₂] at hholder
  have heq := pair_product_rpow (∫⁻ x, F x) (∫⁻ y, G y) (∫⁻ z, H z)
    ((1 : ℝ)/3) (by norm_num)
  exact hholder.trans_eq (by simpa only [show (2 : ℝ)*(1/3) = 2/3 by norm_num] using heq)

end WaveTurbulence.WeylSums
