/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.KinkFT
public import WaveTurbulence.Foundations.VineEst.K2.WeightInt

/-! # W2-KIND2 Lemma A (4): the weighted `L¹` norm of the transform of a kink

`kink_weighted`: for `κ ∈ C²_c`, `0 ≤ α`, `δ > 0`, `α + δ ≤ 1` there is `K` such that for the kinks with poles `{0, d}` (`(p,q) = (0,d)` or `(d,0)`)
`∫⁻ (1+|l|)^α ‖\hat{kink}(l)‖ ≤ K (1+|d|)^{α+δ}`.  This is `env_integral` composed with the pointwise bound of `K2.KinkFT`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem pw_env {X M0 A B d u v : ℝ} (hX : X ≤ M0) (hM0 : 0 ≤ M0) (hA : 0 ≤ A) (hB : 0 ≤ B) (hd : 0 ≤ d) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbd : 1 ≤ u → 1 ≤ v → X ≤ A * d / (u * v) + B * (1 / u ^ 2 + 1 / v ^ 2)) :
    X ≤ (4 * M0 + 4 * A + 4 * B) * ((1 + u) ^ (-(2 : ℝ)) + (1 + v) ^ (-(2 : ℝ)) + d * (1 + u)⁻¹ * (1 + v)⁻¹) := by
  have hr : ∀ w : ℝ, 0 ≤ w → (1 + w) ^ (-(2 : ℝ)) = ((1 + w) ^ 2)⁻¹ := fun w hw => by
    rw [Real.rpow_neg (by linarith), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hr u hu, hr v hv]
  have hu0 : 0 < 1 + u := by linarith
  have hv0 : 0 < 1 + v := by linarith
  have hT : 0 ≤ ((1 + u) ^ 2)⁻¹ + ((1 + v) ^ 2)⁻¹ + d * (1 + u)⁻¹ * (1 + v)⁻¹ := by positivity
  have hTu : 0 ≤ ((1 + u) ^ 2)⁻¹ := by positivity
  have hTv : 0 ≤ ((1 + v) ^ 2)⁻¹ := by positivity
  have hTd : 0 ≤ d * (1 + u)⁻¹ * (1 + v)⁻¹ := by positivity
  by_cases h1 : u < 1
  · have : 1 / 4 ≤ ((1 + u) ^ 2)⁻¹ := by
      rw [← one_div, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    nlinarith
  by_cases h2 : v < 1
  · have : 1 / 4 ≤ ((1 + v) ^ 2)⁻¹ := by
      rw [← one_div, div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
    nlinarith
  push_neg at h1 h2
  have e1 : A * d / (u * v) ≤ 4 * A * (d * (1 + u)⁻¹ * (1 + v)⁻¹) := by
    have hu1 : 0 < u := by linarith
    have hv1 : 0 < v := by linarith
    rw [show A * d / (u * v) = A * d * (u⁻¹ * v⁻¹) by field_simp]
    have a1 : u⁻¹ ≤ 2 * (1 + u)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hu1 hu0]; linarith
    have a2 : v⁻¹ ≤ 2 * (1 + v)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hv1 hv0]; linarith
    calc A * d * (u⁻¹ * v⁻¹) ≤ A * d * ((2 * (1 + u)⁻¹) * (2 * (1 + v)⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (by positivity) (by positivity)) (by positivity)
      _ = 4 * A * (d * (1 + u)⁻¹ * (1 + v)⁻¹) := by ring
  have e2 : B * (1 / u ^ 2) ≤ 4 * B * ((1 + u) ^ 2)⁻¹ := by
    have hu1 : 0 < u := by linarith
    rw [mul_one_div, show 4 * B * ((1 + u) ^ 2)⁻¹ = (4 * B) / (1 + u) ^ 2 by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hB hu1.le]
  have e3 : B * (1 / v ^ 2) ≤ 4 * B * ((1 + v) ^ 2)⁻¹ := by
    have hv1 : 0 < v := by linarith
    rw [mul_one_div, show 4 * B * ((1 + v) ^ 2)⁻¹ = (4 * B) / (1 + v) ^ 2 by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hB hv1.le]
  have := hbd h1 h2
  rw [mul_add] at this
  nlinarith [mul_nonneg hM0 hT, mul_nonneg hA hT]


theorem kink_pointwise {κ : ℝ → ℂ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ) (p q l : ℝ) :
    ‖fT (kinkFn κ p q) l‖ ≤ (4 * (∫ x, ‖κ x‖) + 4 * (‖κ 0‖ / (2 * Real.pi)) + 4 * (kinkC κ / (2 * Real.pi) ^ 2)) *
      ((1 + |l - p|) ^ (-(2 : ℝ)) + (1 + |l - q|) ^ (-(2 : ℝ)) + |p - q| * (1 + |l - p|)⁻¹ * (1 + |l - q|)⁻¹) := by
  have hint : Integrable κ := hκ.continuous.integrable_of_hasCompactSupport hc
  have hM0 : 0 ≤ ∫ x, ‖κ x‖ := integral_nonneg fun x => norm_nonneg _
  have hkC : 0 ≤ kinkC κ := by unfold kinkC; linarith [cb2_nonneg κ, cb2_nonneg (fun y => κ (-y))]
  refine pw_env (norm_fT_le hint p q l) hM0 (by positivity) (by positivity) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) ?_
  intro h1 h2
  have hp : l ≠ p := fun h => by rw [h, sub_self, abs_zero] at h1; linarith
  have hq : l ≠ q := fun h => by rw [h, sub_self, abs_zero] at h2; linarith
  refine (norm_fT_kink_le hκ hc hp hq).trans (le_of_eq ?_)
  have hu : 0 < |l - p| := by linarith
  have hv : 0 < |l - q| := by linarith
  have hpi := Real.pi_pos
  field_simp

theorem kink_weighted {κ : ℝ → ℂ} (hκ : ContDiff ℝ 2 κ) (hc : HasCompactSupport κ) {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ)
    (hαδ : α + δ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p q d : ℝ, ((p = 0 ∧ q = d) ∨ (p = d ∧ q = 0)) →
      ∫⁻ l, ENNReal.ofReal ((1 + |l|) ^ α) * ‖fT (kinkFn κ p q) l‖ₑ ≤ ENNReal.ofReal (K * (1 + |d|) ^ (α + δ)) := by
  obtain ⟨Ke, hKe, hE⟩ := env_integral hα hδ hαδ
  set Cm : ℝ := 4 * (∫ x, ‖κ x‖) + 4 * (‖κ 0‖ / (2 * Real.pi)) + 4 * (kinkC κ / (2 * Real.pi) ^ 2) with hCm
  have hM0 : 0 ≤ ∫ x, ‖κ x‖ := integral_nonneg fun x => norm_nonneg _
  have hkC : 0 ≤ kinkC κ := by unfold kinkC; linarith [cb2_nonneg κ, cb2_nonneg (fun y => κ (-y))]
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  refine ⟨Cm * Ke, mul_nonneg hCm0 hKe, fun p q d hpq => ?_⟩
  obtain ⟨hI, hle⟩ := hE d
  have hpt : ∀ l, ENNReal.ofReal ((1 + |l|) ^ α) * ‖fT (kinkFn κ p q) l‖ₑ ≤ ENNReal.ofReal (Cm * envG α d l) := by
    intro l
    have h := kink_pointwise hκ hc p q l
    have hw : 0 ≤ (1 + |l|) ^ α := by positivity
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hw]
    refine ENNReal.ofReal_le_ofReal ?_
    have hshape : ((1 + |l - p|) ^ (-(2 : ℝ)) + (1 + |l - q|) ^ (-(2 : ℝ)) + |p - q| * (1 + |l - p|)⁻¹ * (1 + |l - q|)⁻¹) =
        (1 + |l|) ^ (-(2 : ℝ)) + (1 + |l - d|) ^ (-(2 : ℝ)) + |d| * (1 + |l|)⁻¹ * (1 + |l - d|)⁻¹ := by
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [abs_sub_comm]
      · simp only [sub_zero, abs_sub_comm 0 p, zero_sub, abs_neg]
        ring
    rw [hshape] at h
    unfold envG
    calc (1 + |l|) ^ α * ‖fT (kinkFn κ p q) l‖ ≤ (1 + |l|) ^ α * (Cm * _) := mul_le_mul_of_nonneg_left h hw
      _ = _ := by ring
  calc ∫⁻ l, ENNReal.ofReal ((1 + |l|) ^ α) * ‖fT (kinkFn κ p q) l‖ₑ ≤ ∫⁻ l, ENNReal.ofReal (Cm * envG α d l) := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ l, Cm * envG α d l) :=
        (ofReal_integral_eq_lintegral_ofReal (hI.const_mul Cm) (Eventually.of_forall fun l => mul_nonneg hCm0 (envG_nonneg α d l))).symm
    _ ≤ ENNReal.ofReal (Cm * Ke * (1 + |d|) ^ (α + δ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        calc Cm * ∫ l, envG α d l ≤ Cm * (Ke * (1 + |d|) ^ (α + δ)) := mul_le_mul_of_nonneg_left hle hCm0
          _ = _ := by ring

end WaveTurbulence.VineEstS5C.P4.W2.K2
