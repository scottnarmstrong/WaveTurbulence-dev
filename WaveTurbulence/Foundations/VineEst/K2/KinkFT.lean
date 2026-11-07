/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.HalfFT
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # W2-KIND2 Lemma A (2): the Fourier transform of a continuous two-slope kink

`kinkFn κ p q x = κ(x) e^{2πi p x}` for `x < 0` and `κ(x) e^{2πi q x}` for `x ≥ 0`.  For `κ ∈ C²_c`:
`‖\hat{kink}(λ)‖ ≤ |κ(0)| |p - q| / (2π |λ-p| |λ-q|) + C (|λ-p|⁻² + |λ-q|⁻²)` (`λ ≠ p, q`), and `‖\hat{kink}(λ)‖ ≤ ‖κ‖_{L¹}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology Complex
open scoped ContDiff

/-- The full-line transform `∫ g(x) e^{-2πi λ x} dx`. -/
noncomputable def fT (g : ℝ → ℂ) (l : ℝ) : ℂ := ∫ x, g x * ex l x

/-- The two-slope kink. -/
noncomputable def kinkFn (κ : ℝ → ℂ) (p q : ℝ) (x : ℝ) : ℂ :=
  if x < 0 then κ x * ex (-p) x else κ x * ex (-q) x

theorem kinkFn_of_nonpos {κ : ℝ → ℂ} {p q x : ℝ} (hx : x ≤ 0) : kinkFn κ p q x = κ x * ex (-p) x := by
  unfold kinkFn
  by_cases h : x < 0
  · simp [h]
  · have : x = 0 := le_antisymm hx (not_lt.1 h)
    subst this
    simp [h, ex_zero]

theorem kinkFn_of_pos {κ : ℝ → ℂ} {p q x : ℝ} (hx : 0 < x) : kinkFn κ p q x = κ x * ex (-q) x := by
  unfold kinkFn
  simp [not_lt.2 hx.le]

theorem norm_kinkFn_le (κ : ℝ → ℂ) (p q x : ℝ) : ‖kinkFn κ p q x‖ ≤ ‖κ x‖ := by
  unfold kinkFn
  split_ifs <;> simp [norm_ex]

theorem measurable_kinkFn {κ : ℝ → ℂ} (hκ : Measurable κ) (p q : ℝ) : Measurable (kinkFn κ p q) := by
  unfold kinkFn
  refine Measurable.ite measurableSet_Iio (hκ.mul ?_) (hκ.mul ?_) <;>
  · exact (continuous_ex _).measurable

theorem integrable_kinkFn {κ : ℝ → ℂ} (hκ : Continuous κ) (hc : HasCompactSupport κ) (p q : ℝ) :
    Integrable (kinkFn κ p q) :=
  (hκ.integrable_of_hasCompactSupport hc).norm.mono' (measurable_kinkFn hκ.measurable p q).aestronglyMeasurable
    (Eventually.of_forall fun x => norm_kinkFn_le κ p q x)

theorem norm_fT_le {κ : ℝ → ℂ} (hκ : Integrable κ) (p q l : ℝ) : ‖fT (kinkFn κ p q) l‖ ≤ ∫ x, ‖κ x‖ := by
  unfold fT
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hκ.norm (Eventually.of_forall fun x => ?_)
  show ‖kinkFn κ p q x * ex l x‖ ≤ ‖κ x‖
  rw [norm_mul, norm_ex, mul_one]
  exact norm_kinkFn_le κ p q x

/-- **The transform of the kink in terms of half-line transforms.** -/
theorem fT_kink {κ : ℝ → ℂ} (hκ : Continuous κ) (hc : HasCompactSupport κ) (p q l : ℝ) :
    fT (kinkFn κ p q) l = hft (fun y => κ (-y)) (p - l) + hft κ (l - q) := by
  have hi : Integrable (fun x => kinkFn κ p q x * ex l x) := by
    refine ((hκ.integrable_of_hasCompactSupport hc).norm.mono' ?_ (Eventually.of_forall fun x => ?_))
    · exact ((measurable_kinkFn hκ.measurable p q).mul (continuous_ex l).measurable).aestronglyMeasurable
    · show ‖kinkFn κ p q x * ex l x‖ ≤ ‖κ x‖
      rw [norm_mul, norm_ex, mul_one]; exact norm_kinkFn_le κ p q x
  unfold fT hft
  rw [← intervalIntegral.integral_Iic_add_Ioi hi.integrableOn hi.integrableOn]
  congr 1
  · have e1 : ∫ x in Iic (0 : ℝ), kinkFn κ p q x * ex l x = ∫ x in Iic (0 : ℝ), (fun y => κ (-y) * ex (p - l) y) (-x) := by
      refine setIntegral_congr_fun measurableSet_Iic fun x hx => ?_
      simp only [neg_neg]
      rw [kinkFn_of_nonpos hx, mul_assoc, ex_add, ex_neg_arg, show (-p + l) = -(p - l) by ring]
    rw [e1, integral_comp_neg_Iic (0 : ℝ) (fun y => κ (-y) * ex (p - l) y), neg_zero]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [kinkFn_of_pos hx, mul_assoc, ex_add, show (-q + l) = l - q by ring]


theorem cb2_nonneg (g : ℝ → ℂ) : 0 ≤ cb2 g := by
  unfold cb2
  exact add_nonneg (norm_nonneg _) (integral_nonneg fun x => norm_nonneg _)

/-- The symmetric constant of the kink bound. -/
noncomputable def kinkC (κ : ℝ → ℂ) : ℝ := cb2 κ + cb2 (fun y => κ (-y))

/-- **Pointwise bound of the kink transform.** -/
theorem norm_fT_kink_le {κ : ℝ → ℂ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ) {p q l : ℝ}
    (hp : l ≠ p) (hq : l ≠ q) :
    ‖fT (kinkFn κ p q) l‖ ≤ ‖κ 0‖ * |p - q| / (2 * Real.pi * |l - p| * |l - q|) +
      kinkC κ * (1 / (2 * Real.pi * |l - p|) ^ 2 + 1 / (2 * Real.pi * |l - q|) ^ 2) := by
  have hκc : Continuous κ := hκ.continuous
  have hh : ContDiff ℝ 2 (fun y => κ (-y)) := hκ.comp contDiff_neg
  have hhc : HasCompactSupport (fun y => κ (-y)) := hc.comp_homeomorph (Homeomorph.neg ℝ)
  have hpl : p - l ≠ 0 := sub_ne_zero.2 (Ne.symm hp)
  have hlq : l - q ≠ 0 := sub_ne_zero.2 hq
  rw [fT_kink hκc hc p q l, hft_expand hh hhc hpl, hft_expand hκ hc hlq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpl' : ((p - l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpl
  have hlq' : ((l - q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlq
  set s1 : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((p - l : ℝ) : ℂ) with hs1
  set s2 : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((l - q : ℝ) : ℂ) with hs2
  have hlead : κ 0 / s1 + κ 0 / s2 = κ 0 * ((p - q : ℝ) : ℂ) / (2 * (Real.pi : ℂ) * Complex.I * ((p - l : ℝ) : ℂ) * ((l - q : ℝ) : ℂ)) := by
    rw [hs1, hs2]
    push_cast at hpl' hlq' ⊢
    field_simp
    ring
  have hlead_norm : ‖κ 0 / s1 + κ 0 / s2‖ = ‖κ 0‖ * |p - q| / (2 * Real.pi * |l - p| * |l - q|) := by
    rw [hlead, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      norm_mul, norm_mul, Complex.norm_I]
    simp only [Real.norm_eq_abs, norm_ofNat, Complex.norm_real, abs_of_pos Real.pi_pos, mul_one]
    rw [abs_sub_comm p l]
  have h1 := norm_remainder_le hh hhc hpl
  have h2 := norm_remainder_le hκ hc hlq
  have c1 : cb2 (fun y => κ (-y)) ≤ kinkC κ := by unfold kinkC; linarith [cb2_nonneg κ]
  have c2 : cb2 κ ≤ kinkC κ := by unfold kinkC; linarith [cb2_nonneg (fun y => κ (-y))]
  have hpos1 : 0 < (2 * Real.pi * |p - l|) ^ 2 := by have := abs_pos.2 hpl; positivity
  have hpos2 : 0 < (2 * Real.pi * |l - q|) ^ 2 := by have := abs_pos.2 hlq; positivity
  have h1' : ‖deriv (fun y => κ (-y)) 0 / s1 ^ 2 + hft (deriv (deriv fun y => κ (-y))) (p - l) / s1 ^ 2‖ ≤
      kinkC κ * (1 / (2 * Real.pi * |l - p|) ^ 2) := by
    rw [abs_sub_comm l p, ← div_eq_mul_one_div]
    exact h1.trans (div_le_div_of_nonneg_right c1 hpos1.le)
  have h2' : ‖deriv κ 0 / s2 ^ 2 + hft (deriv (deriv κ)) (l - q) / s2 ^ 2‖ ≤
      kinkC κ * (1 / (2 * Real.pi * |l - q|) ^ 2) := by
    rw [← div_eq_mul_one_div]
    exact h2.trans (div_le_div_of_nonneg_right c2 hpos2.le)
  rw [neg_zero]
  calc _ = ‖(κ 0 / s1 + κ 0 / s2) + ((deriv (fun y => κ (-y)) 0 / s1 ^ 2 + hft (deriv (deriv fun y => κ (-y))) (p - l) / s1 ^ 2) +
        (deriv κ 0 / s2 ^ 2 + hft (deriv (deriv κ)) (l - q) / s2 ^ 2))‖ := by congr 1; ring
    _ ≤ ‖κ 0 / s1 + κ 0 / s2‖ + (‖deriv (fun y => κ (-y)) 0 / s1 ^ 2 + hft (deriv (deriv fun y => κ (-y))) (p - l) / s1 ^ 2‖ +
        ‖deriv κ 0 / s2 ^ 2 + hft (deriv (deriv κ)) (l - q) / s2 ^ 2‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ _ := by
        rw [hlead_norm]
        nlinarith [h1', h2']

end WaveTurbulence.VineEstS5C.P4.W2.K2
