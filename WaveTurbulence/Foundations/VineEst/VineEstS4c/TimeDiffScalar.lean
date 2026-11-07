/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

import Mathlib.Tactic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# V5 Step 4c, clause (c): the scalar scale integral

For `μ ∈ ℝ` and exponents `0 ≤ θ < b`, `b + θ < 1` the Gamma-mixture parameter `s ∈ (0, ∞)` integral
`∫ s^{b/2 - 1} ((1+s)(1+μ²/s))^{θ/2} min(1, |μ|/√s) ds` is `≲ (1+μ²)^{(b+θ)/2}`.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set Real
open scoped ENNReal

namespace WaveTurbulence.VineEstS4c.TimeDiff

/-- `∫⁻_{(0,m]} s^p` for `p > -1`. -/
theorem lintegral_Ioc_rpow {p : ℝ} (hp : -1 < p) {m : ℝ} (hm : 0 < m) :
    ∫⁻ s in Ioc 0 m, ENNReal.ofReal (s ^ p) = ENNReal.ofReal (m ^ (p + 1) / (p + 1)) := by
  have hi : IntegrableOn (fun s : ℝ => s ^ p) (Ioc 0 m) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m) hp)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hm.le).mp this
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs =>
      Real.rpow_nonneg hs.1.le p))]
  congr 1
  rw [← intervalIntegral.integral_of_le hm.le, integral_rpow (Or.inl hp)]
  have : (0 : ℝ) ^ (p + 1) = 0 := Real.zero_rpow (by linarith)
  rw [this, sub_zero]

/-- `∫⁻_{(m,∞)} s^p` for `p < -1`. -/
theorem lintegral_Ioi_rpow {p : ℝ} (hp : p < -1) {m : ℝ} (hm : 0 < m) :
    ∫⁻ s in Ioi m, ENNReal.ofReal (s ^ p) = ENNReal.ofReal (-m ^ (p + 1) / (p + 1)) := by
  have hi := integrableOn_Ioi_rpow_of_lt hp hm
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun s hs =>
      Real.rpow_nonneg (hm.trans hs).le p))]
  rw [integral_Ioi_rpow_of_lt hp hm]

/-- The integrand of the scale integral. -/
@[expose] noncomputable def scaleInt (b θ μ s : ℝ) : ℝ :=
  s ^ (b / 2 - 1) * (((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) * min 1 (|μ| / √s))

theorem scaleInt_nonneg (b θ μ : ℝ) {s : ℝ} (hs : 0 < s) : 0 ≤ scaleInt b θ μ s := by
  unfold scaleInt
  have : 0 ≤ min 1 (|μ| / √s) := le_min zero_le_one (by positivity)
  positivity

theorem scaleInt_le_low {b θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (μ : ℝ) {s : ℝ} (hs : 0 < s)
    (hsm : s ≤ 1 + μ ^ 2) :
    scaleInt b θ μ s ≤ (4 * (1 + μ ^ 2)) ^ (θ / 2) *
      (s ^ (b / 2 - 1) + s ^ ((b - θ) / 2 - 1)) := by
  unfold scaleInt
  set m := 1 + μ ^ 2 with hm
  have hm1 : 1 ≤ m := by nlinarith [sq_nonneg μ]
  have h1 : (1 + s) * (1 + μ ^ 2 / s) ≤ 4 * m * (1 + 1 / s) := by
    have hμ : μ ^ 2 ≤ m := by rw [hm]; linarith
    have h2 : μ ^ 2 / s ≤ m / s := div_le_div_of_nonneg_right hμ hs.le
    have h3 : (1 + s) * (1 + μ ^ 2 / s) = 1 + s + μ ^ 2 + μ ^ 2 / s := by
      have : s * (μ ^ 2 / s) = μ ^ 2 := by field_simp
      calc (1 + s) * (1 + μ ^ 2 / s) = 1 + s + μ ^ 2 / s + s * (μ ^ 2 / s) := by ring
        _ = _ := by rw [this]; ring
    rw [h3]
    have : m / s ≤ m * (1 / s) := by rw [mul_one_div]
    have h5 : 0 ≤ m * (1 / s) := by positivity
    nlinarith
  have hpos : 0 ≤ (1 + s) * (1 + μ ^ 2 / s) := by positivity
  have h4 : ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) ≤ (4 * m * (1 + 1 / s)) ^ (θ / 2) :=
    Real.rpow_le_rpow hpos h1 (by linarith)
  have h5 : (4 * m * (1 + 1 / s)) ^ (θ / 2) = (4 * m) ^ (θ / 2) * (1 + 1 / s) ^ (θ / 2) :=
    Real.mul_rpow (by positivity) (by positivity)
  have h6 : (1 + 1 / s) ^ (θ / 2) ≤ 1 + (1 / s) ^ (θ / 2) := by
    have := Real.rpow_add_le_add_rpow (zero_le_one : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ 1 / s)
      (by linarith : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ 1)
    simpa using this
  have hmin : min 1 (|μ| / √s) ≤ 1 := min_le_left _ _
  have hmin0 : 0 ≤ min 1 (|μ| / √s) := le_min zero_le_one (by positivity)
  have hA : 0 ≤ ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) := Real.rpow_nonneg hpos _
  have hsp : 0 ≤ s ^ (b / 2 - 1) := Real.rpow_nonneg hs.le _
  have hc : 0 ≤ (4 * m) ^ (θ / 2) := Real.rpow_nonneg (by positivity) _
  have key : ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) ≤ (4 * m) ^ (θ / 2) * (1 + (1 / s) ^ (θ / 2)) :=
    h4.trans (h5.le.trans (mul_le_mul_of_nonneg_left h6 hc))
  calc s ^ (b / 2 - 1) * (((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) * min 1 (|μ| / √s))
      ≤ s ^ (b / 2 - 1) * (((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) * 1) := by
        gcongr
    _ ≤ s ^ (b / 2 - 1) * ((4 * m) ^ (θ / 2) * (1 + (1 / s) ^ (θ / 2))) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left key hsp
    _ = (4 * m) ^ (θ / 2) * (s ^ (b / 2 - 1) + s ^ ((b - θ) / 2 - 1)) := by
        have : s ^ (b / 2 - 1) * (1 / s) ^ (θ / 2) = s ^ ((b - θ) / 2 - 1) := by
          rw [one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
          congr 1; ring
        calc _ = (4 * m) ^ (θ / 2) * (s ^ (b / 2 - 1) +
              s ^ (b / 2 - 1) * (1 / s) ^ (θ / 2)) := by ring
          _ = _ := by rw [this]

theorem scaleInt_le_high {b θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (μ : ℝ) {s : ℝ} (hs : 0 < s)
    (hsm : 1 + μ ^ 2 < s) :
    scaleInt b θ μ s ≤ 4 ^ (θ / 2) * √(1 + μ ^ 2) * s ^ ((b + θ - 1) / 2 - 1) := by
  unfold scaleInt
  set m := 1 + μ ^ 2 with hm
  have hm1 : 1 ≤ m := by nlinarith [sq_nonneg μ]
  have hpos : 0 ≤ (1 + s) * (1 + μ ^ 2 / s) := by positivity
  have h1 : (1 + s) * (1 + μ ^ 2 / s) ≤ 4 * s := by
    have hs1 : 1 ≤ s := by linarith
    have : μ ^ 2 / s ≤ 1 := by
      rw [div_le_one hs]; linarith
    nlinarith
  have h4 : ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) ≤ (4 * s) ^ (θ / 2) :=
    Real.rpow_le_rpow hpos h1 (by linarith)
  have h5 : (4 * s) ^ (θ / 2) = 4 ^ (θ / 2) * s ^ (θ / 2) :=
    Real.mul_rpow (by norm_num) hs.le
  have hmin : min 1 (|μ| / √s) ≤ √m / √s := by
    refine (min_le_right _ _).trans ?_
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by rw [hm]; linarith)
  have hmin0 : 0 ≤ min 1 (|μ| / √s) := le_min zero_le_one (by positivity)
  have hA : 0 ≤ ((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) := Real.rpow_nonneg hpos _
  have hsq : √s = s ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow s
  have hsp : 0 ≤ s ^ (b / 2 - 1) := Real.rpow_nonneg hs.le _
  calc s ^ (b / 2 - 1) * (((1 + s) * (1 + μ ^ 2 / s)) ^ (θ / 2) * min 1 (|μ| / √s))
      ≤ s ^ (b / 2 - 1) * ((4 ^ (θ / 2) * s ^ (θ / 2)) * (√m / √s)) := by
        gcongr
        exact h4.trans_eq h5
    _ = 4 ^ (θ / 2) * √m * s ^ ((b + θ - 1) / 2 - 1) := by
        have : s ^ (b / 2 - 1) * s ^ (θ / 2) / √s = s ^ ((b + θ - 1) / 2 - 1) := by
          rw [hsq, ← Real.rpow_add hs, ← Real.rpow_sub hs]
          congr 1; ring
        calc _ = 4 ^ (θ / 2) * √m * (s ^ (b / 2 - 1) * s ^ (θ / 2) / √s) := by ring
          _ = _ := by rw [this]


theorem lintegral_ofReal_le_integral {S : Set ℝ} (hS : MeasurableSet S) {f g : ℝ → ℝ}
    (hg : IntegrableOn g S) (hg0 : ∀ s ∈ S, 0 ≤ g s) (hfg : ∀ s ∈ S, f s ≤ g s) :
    ∫⁻ s in S, ENNReal.ofReal (f s) ≤ ENNReal.ofReal (∫ s in S, g s) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg
    ((ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall hg0))]
  exact lintegral_mono_ae ((ae_restrict_iff' hS).mpr (Filter.Eventually.of_forall fun s hs =>
    ENNReal.ofReal_le_ofReal (hfg s hs)))

theorem integrableOn_Ioc_rpow {p : ℝ} (hp : -1 < p) {m : ℝ} (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => s ^ p) (Ioc 0 m) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hm.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := m) hp)

theorem integral_Ioc_rpow {p : ℝ} (hp : -1 < p) {m : ℝ} (hm : 0 < m) :
    ∫ s in Ioc 0 m, s ^ p = m ^ (p + 1) / (p + 1) := by
  rw [← intervalIntegral.integral_of_le hm.le, integral_rpow (Or.inl hp)]
  have : (0 : ℝ) ^ (p + 1) = 0 := Real.zero_rpow (by linarith)
  rw [this, sub_zero]

/-- **The scale integral**: `∫_0^∞ s^{b/2-1}((1+s)(1+μ²/s))^{θ/2} min(1,|μ|/√s) ds ≲ (1+μ²)^{(b+θ)/2}`. -/
theorem lintegral_scaleInt_le {b θ : ℝ} (hθ0 : 0 ≤ θ) (hθb : θ < b) (hbθ : b + θ < 1) (μ : ℝ) :
    ∫⁻ s in Ioi 0, ENNReal.ofReal (scaleInt b θ μ s) ≤
      ENNReal.ofReal (4 ^ (θ / 2) * (2 / b + 2 / (b - θ) + 2 / (1 - b - θ)) *
        (1 + μ ^ 2) ^ ((b + θ) / 2)) := by
  set m := 1 + μ ^ 2 with hm
  have hm1 : 1 ≤ m := by nlinarith [sq_nonneg μ]
  have hm0 : 0 < m := by linarith
  have hb : 0 < b := by linarith
  have hθ1 : θ ≤ 1 := by linarith
  have hsplit : Ioi (0 : ℝ) = Ioc 0 m ∪ Ioi m := (Ioc_union_Ioi_eq_Ioi hm0.le).symm
  rw [hsplit, lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  have h4 : (0 : ℝ) < 4 ^ (θ / 2) := by positivity
  -- low part
  have hlow : ∫⁻ s in Ioc 0 m, ENNReal.ofReal (scaleInt b θ μ s) ≤
      ENNReal.ofReal (4 ^ (θ / 2) * (2 / b + 2 / (b - θ)) * m ^ ((b + θ) / 2)) := by
    have hi1 := integrableOn_Ioc_rpow (p := b / 2 - 1) (by linarith) hm0
    have hi2 := integrableOn_Ioc_rpow (p := (b - θ) / 2 - 1) (by linarith) hm0
    refine (lintegral_ofReal_le_integral measurableSet_Ioc
      (g := fun s => (4 * m) ^ (θ / 2) * (s ^ (b / 2 - 1) + s ^ ((b - θ) / 2 - 1)))
      ((hi1.add hi2).const_mul _) (fun s hs => by
        have := Real.rpow_nonneg hs.1.le (b / 2 - 1)
        have := Real.rpow_nonneg hs.1.le ((b - θ) / 2 - 1)
        positivity) (fun s hs => scaleInt_le_low hθ0 hθ1 μ hs.1 hs.2)).trans ?_
    rw [integral_const_mul, integral_add hi1 hi2, integral_Ioc_rpow (by linarith) hm0,
      integral_Ioc_rpow (by linarith) hm0]
    apply ENNReal.ofReal_le_ofReal
    have e1 : b / 2 - 1 + 1 = b / 2 := by ring
    have e2 : (b - θ) / 2 - 1 + 1 = (b - θ) / 2 := by ring
    rw [e1, e2, Real.mul_rpow (by norm_num) hm0.le]
    have h4' : (4 : ℝ) ^ (θ / 2) = 4 ^ (θ / 2) := rfl
    have f1 : m ^ ((b - θ) / 2) ≤ m ^ (b / 2) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    have f2 : m ^ (θ / 2) * m ^ (b / 2) = m ^ ((b + θ) / 2) := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    have f3 : (0 : ℝ) ≤ m ^ (θ / 2) := by positivity
    have f4 : (0 : ℝ) ≤ m ^ (b / 2) := by positivity
    have f5 : 0 < b - θ := by linarith
    have : b / 2 / (b / 2) = 1 := div_self (by positivity)
    have g1 : m ^ (b / 2) / (b / 2) = 2 / b * m ^ (b / 2) := by field_simp
    have g2 : m ^ ((b - θ) / 2) / ((b - θ) / 2) = 2 / (b - θ) * m ^ ((b - θ) / 2) := by
      field_simp
    rw [g1, g2]
    have : 2 / (b - θ) * m ^ ((b - θ) / 2) ≤ 2 / (b - θ) * m ^ (b / 2) :=
      mul_le_mul_of_nonneg_left f1 (by positivity)
    calc 4 ^ (θ / 2) * m ^ (θ / 2) * (2 / b * m ^ (b / 2) + 2 / (b - θ) * m ^ ((b - θ) / 2))
        ≤ 4 ^ (θ / 2) * m ^ (θ / 2) * (2 / b * m ^ (b / 2) + 2 / (b - θ) * m ^ (b / 2)) := by
          gcongr
      _ = 4 ^ (θ / 2) * (2 / b + 2 / (b - θ)) * (m ^ (θ / 2) * m ^ (b / 2)) := by ring
      _ = _ := by rw [f2]
  -- high part
  have hhigh : ∫⁻ s in Ioi m, ENNReal.ofReal (scaleInt b θ μ s) ≤
      ENNReal.ofReal (4 ^ (θ / 2) * (2 / (1 - b - θ)) * m ^ ((b + θ) / 2)) := by
    have hexp : (b + θ - 1) / 2 - 1 < -1 := by linarith
    have hi := integrableOn_Ioi_rpow_of_lt hexp hm0
    refine (lintegral_ofReal_le_integral measurableSet_Ioi
      (g := fun s => 4 ^ (θ / 2) * √m * s ^ ((b + θ - 1) / 2 - 1))
      (hi.const_mul _) (fun s hs => by
        have := Real.rpow_nonneg (hm0.trans hs).le ((b + θ - 1) / 2 - 1)
        positivity) (fun s hs => scaleInt_le_high hθ0 hθ1 μ (hm0.trans hs) hs)).trans ?_
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hm0]
    apply ENNReal.ofReal_le_ofReal
    have e1 : (b + θ - 1) / 2 - 1 + 1 = (b + θ - 1) / 2 := by ring
    rw [e1]
    have hsq : √m = m ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow m
    have f2 : m ^ (1 / 2 : ℝ) * m ^ ((b + θ - 1) / 2) = m ^ ((b + θ) / 2) := by
      rw [← Real.rpow_add hm0]; congr 1; ring
    have f5 : 0 < 1 - b - θ := by linarith
    have g1 : -m ^ ((b + θ - 1) / 2) / ((b + θ - 1) / 2) =
        2 / (1 - b - θ) * m ^ ((b + θ - 1) / 2) := by
      have hq : (b + θ - 1) / 2 = -((1 - b - θ) / 2) := by ring
      have hq0 : (1 - b - θ) ≠ 0 := f5.ne'
      rw [hq, neg_div_neg_eq]
      field_simp
    rw [g1, hsq]
    apply le_of_eq
    calc 4 ^ (θ / 2) * m ^ (1 / 2 : ℝ) * (2 / (1 - b - θ) * m ^ ((b + θ - 1) / 2))
        = 4 ^ (θ / 2) * (2 / (1 - b - θ)) * (m ^ (1 / 2 : ℝ) * m ^ ((b + θ - 1) / 2)) := by ring
      _ = _ := by rw [f2]
  refine (add_le_add hlow hhigh).trans ?_
  have c1 : 0 < 2 / (b - θ) := div_pos two_pos (by linarith)
  have c2 : 0 < 2 / (1 - b - θ) := div_pos two_pos (by linarith)
  have c3 : 0 < 2 / b := div_pos two_pos hb
  have c4 : (0 : ℝ) < m ^ ((b + θ) / 2) := by positivity
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

end WaveTurbulence.VineEstS4c.TimeDiff
