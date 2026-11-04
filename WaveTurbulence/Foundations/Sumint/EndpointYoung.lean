/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CubicYoung
import Mathlib.Tactic

/-!
# Asymmetric Young inequality for the two-exit Fourier endpoint

The exponents are 3/2, 6/5 and 2. Hölder on the pair products has
weights 1/2, 1/3 and 1/6, respectively. This retains the L² input
needed for the endpoint Plancherel estimate.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- Weighted pair products collect their scalar powers exactly, including infinite values. -/
theorem pair_product_weighted (x y z : ℝ≥0∞) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (x*y)^a*(y*z)^b*(z*x)^c = x^(a+c)*y^(a+b)*z^(b+c) := by
  rw [ENNReal.mul_rpow_of_nonneg x y ha, ENNReal.mul_rpow_of_nonneg y z hb,
    ENNReal.mul_rpow_of_nonneg z x hc]
  calc
    _ = (x^a*x^c)*(y^a*y^b)*(z^b*z^c) := by ac_rfl
    _ = _ := by
      rw [← ENNReal.rpow_add_of_nonneg a c ha hc,
        ← ENNReal.rpow_add_of_nonneg a b ha hb,
        ← ENNReal.rpow_add_of_nonneg b c hb hc]

/-- The asymmetric three-factor Young bound at the two-exit endpoint. -/
theorem lintegral_triple_add_le_endpoint (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    (∫⁻ xy : ℝ × ℝ, f xy.1*g xy.2*h (xy.1+xy.2)) ≤
      (∫⁻ x : ℝ, f x^((3:ℝ)/2))^((2:ℝ)/3) *
      (∫⁻ y : ℝ, g y^((6:ℝ)/5))^((5:ℝ)/6) *
      (∫⁻ z : ℝ, h z^(2:ℝ))^((1:ℝ)/2) := by
  let F : ℝ → ℝ≥0∞ := fun x => f x^((3:ℝ)/2)
  let G : ℝ → ℝ≥0∞ := fun x => g x^((6:ℝ)/5)
  let H : ℝ → ℝ≥0∞ := fun x => h x^(2:ℝ)
  have hF : Measurable F := hf.pow_const _
  have hG : Measurable G := hg.pow_const _
  have hH : Measurable H := hh.pow_const _
  let P : Fin 3 → (ℝ × ℝ) → ℝ≥0∞ :=
    ![fun xy => F xy.1*G xy.2, fun xy => G xy.2*H (xy.1+xy.2), fun xy => H (xy.1+xy.2)*F xy.1]
  let p : Fin 3 → ℝ := ![1/2,1/3,1/6]
  have hP (i : Fin 3) : AEMeasurable (P i) volume := by
    fin_cases i
    · exact ((hF.comp measurable_fst).mul (hG.comp measurable_snd)).aemeasurable
    · exact ((hG.comp measurable_snd).mul (hH.comp (measurable_fst.add measurable_snd))).aemeasurable
    · exact ((hH.comp (measurable_fst.add measurable_snd)).mul (hF.comp measurable_fst)).aemeasurable
  have hprod (xy : ℝ × ℝ) : (∏ i : Fin 3, (P i xy)^(p i)) = f xy.1*g xy.2*h (xy.1+xy.2) := by
    simp only [P,p,Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
    change (F xy.1*G xy.2)^((1:ℝ)/2)*(G xy.2*H (xy.1+xy.2))^((1:ℝ)/3)*
      (H (xy.1+xy.2)*F xy.1)^((1:ℝ)/6) = _
    rw [pair_product_weighted _ _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    simp only [F,G,H,← ENNReal.rpow_mul]
    norm_num
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
  have hsum : ∑ i : Fin 3, p i = 1 := by simp [p, Fin.sum_univ_three]; norm_num
  have hp (i : Fin 3) : 0 ≤ p i := by fin_cases i <;> norm_num [p]
  have hholder := ENNReal.lintegral_prod_norm_pow_le (μ := (volume : Measure (ℝ × ℝ)))
    (univ : Finset (Fin 3)) (f := P) (fun i _ => hP i)
    (p := p) (by simpa using hsum) (fun i _ => hp i)
  simp_rw [hprod] at hholder
  simp only [Fin.prod_univ_three,p,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    hI₀,hI₁,hI₂] at hholder
  have heq := pair_product_weighted (∫⁻ x, F x) (∫⁻ y, G y) (∫⁻ z, H z)
    ((1:ℝ)/2) ((1:ℝ)/3) ((1:ℝ)/6) (by norm_num) (by norm_num) (by norm_num)
  exact hholder.trans_eq (by norm_num [F,G,H] at heq ⊢; exact heq)

end WaveTurbulence.Sumint
