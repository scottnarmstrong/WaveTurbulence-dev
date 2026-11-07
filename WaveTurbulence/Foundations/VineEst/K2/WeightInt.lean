/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! # W2-KIND2 Lemma A (3): weighted integrals of the kink envelope

`env_integral`: for `0 ≤ α < 1`, `δ > 0` there is `K` with, for all `d`,
`∫ (1+|l|)^α ((1+|l|)^{-2} + (1+|l-d|)^{-2} + |d| (1+|l|)^{-1} (1+|l-d|)^{-1}) dl ≤ K (1+|d|)^{α+δ}` (integrable).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2.K2
open MeasureTheory Set Filter Topology

theorem integrable_pow_decay {r : ℝ} (hr : 1 < r) : Integrable (fun x : ℝ => (1 + |x|) ^ (-r)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa using this

theorem integrable_pow_decay_shift {r : ℝ} (hr : 1 < r) (d : ℝ) : Integrable (fun l : ℝ => (1 + |l - d|) ^ (-r)) :=
  (integrable_pow_decay hr).comp_sub_right d

theorem integral_pow_decay_shift {r : ℝ} (d : ℝ) :
    ∫ l : ℝ, (1 + |l - d|) ^ (-r) = ∫ x : ℝ, (1 + |x|) ^ (-r) :=
  integral_sub_right_eq_self (fun x : ℝ => (1 + |x|) ^ (-r)) d

theorem one_add_abs_le_mul (l d : ℝ) : 1 + |l| ≤ (1 + |d|) * (1 + |l - d|) := by
  have h1 : |l| ≤ |d| + |l - d| := by
    calc |l| = |d + (l - d)| := by ring_nf
      _ ≤ |d| + |l - d| := abs_add_le _ _
  nlinarith [abs_nonneg d, abs_nonneg (l - d)]


/-- The pointwise cross-term bound. `a = 1 + |l|`, `b = 1 + |l - d|`, `S = 1 + d0`, `d0 = |d|`. -/
theorem cross_pointwise {α δ a b d0 : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hαδ : α + δ ≤ 1) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hd0 : 0 ≤ d0) (h1 : d0 ≤ a + b) (h2 : a ≤ b + d0) (h3 : b ≤ a + d0) :
    a ^ α * (d0 * a⁻¹ * b⁻¹) ≤ (2 * 4 ^ (α + δ) + 2) * (1 + d0) ^ (α + δ) * (a ^ (-(1 + δ)) + b ^ (-(1 + δ))) := by
  set S := 1 + d0 with hS
  have hS1 : 1 ≤ S := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hSd : 0 < S := by linarith
  have hC : 0 ≤ (2 * (4 : ℝ) ^ (α + δ) + 2) := by positivity
  have hSp : 0 ≤ S ^ (α + δ) := by positivity
  by_cases hnear : a ≤ 3 * S
  · -- near region: a ≤ 3S, b ≤ a + d0 ≤ 4S
    have hb4 : b ≤ 4 * S := by linarith
    have e1 : d0 * a⁻¹ * b⁻¹ ≤ a⁻¹ + b⁻¹ := by
      rw [show d0 * a⁻¹ * b⁻¹ = d0 / (a * b) by field_simp]
      rw [div_le_iff₀ (by positivity)]
      have : (a⁻¹ + b⁻¹) * (a * b) = a + b := by field_simp; ring
      rw [this]; exact h1
    have e2 : a ^ α ≤ (4 * S) ^ α := Real.rpow_le_rpow ha0.le (by linarith) hα
    have e3 : a⁻¹ ≤ (4 * S) ^ δ * a ^ (-(1 + δ)) := by
      have : a ^ δ ≤ (4 * S) ^ δ := Real.rpow_le_rpow ha0.le (by linarith) hδ.le
      calc a⁻¹ = a ^ δ * a ^ (-(1 + δ)) := by
            rw [← Real.rpow_add ha0]; rw [show δ + -(1 + δ) = -1 by ring, Real.rpow_neg_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
    have e4 : b⁻¹ ≤ (4 * S) ^ δ * b ^ (-(1 + δ)) := by
      have : b ^ δ ≤ (4 * S) ^ δ := Real.rpow_le_rpow hb0.le hb4 hδ.le
      calc b⁻¹ = b ^ δ * b ^ (-(1 + δ)) := by
            rw [← Real.rpow_add hb0]; rw [show δ + -(1 + δ) = -1 by ring, Real.rpow_neg_one]
        _ ≤ _ := mul_le_mul_of_nonneg_right this (by positivity)
    have e5 : (4 * S) ^ α * (4 * S) ^ δ = 4 ^ (α + δ) * S ^ (α + δ) := by
      rw [← Real.rpow_add (by positivity), Real.mul_rpow (by norm_num) hSd.le]
    calc a ^ α * (d0 * a⁻¹ * b⁻¹) ≤ (4 * S) ^ α * (a⁻¹ + b⁻¹) :=
          mul_le_mul e2 e1 (by positivity) (by positivity)
      _ ≤ (4 * S) ^ α * ((4 * S) ^ δ * a ^ (-(1 + δ)) + (4 * S) ^ δ * b ^ (-(1 + δ))) :=
          mul_le_mul_of_nonneg_left (add_le_add e3 e4) (by positivity)
      _ = 4 ^ (α + δ) * S ^ (α + δ) * (a ^ (-(1 + δ)) + b ^ (-(1 + δ))) := by rw [← e5]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (α + δ)]
  · -- far region: a > 3S, b ≥ a - d0 ≥ 2a/3
    have hfar : 3 * S < a := lt_of_not_ge hnear
    have hb2 : 2 * a / 3 ≤ b := by linarith
    have hb3 : 0 < b := hb0
    have e1 : d0 * a⁻¹ * b⁻¹ ≤ 3 / 2 * d0 * a ^ (-(2 : ℝ)) := by
      have : b⁻¹ ≤ 3 / 2 * a⁻¹ := by
        have hb2' : 2 / 3 * a ≤ b := by linarith
        have key : 1 ≤ 3 / 2 * a⁻¹ * b := by
          calc (1 : ℝ) = 3 / 2 * a⁻¹ * (2 / 3 * a) := by field_simp
            _ ≤ 3 / 2 * a⁻¹ * b := mul_le_mul_of_nonneg_left hb2' (by positivity)
        calc b⁻¹ = 1 * b⁻¹ := (one_mul _).symm
          _ ≤ (3 / 2 * a⁻¹ * b) * b⁻¹ := mul_le_mul_of_nonneg_right key (by positivity)
          _ = 3 / 2 * a⁻¹ := by field_simp
      calc d0 * a⁻¹ * b⁻¹ ≤ d0 * a⁻¹ * (3 / 2 * a⁻¹) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = 3 / 2 * d0 * a ^ (-(2 : ℝ)) := by
            rw [Real.rpow_neg ha0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            field_simp
    have hexp : a ^ α * a ^ (-(2 : ℝ)) = a ^ (α - 1 + δ) * a ^ (-(1 + δ)) := by
      rw [← Real.rpow_add ha0, ← Real.rpow_add ha0]; congr 1; ring
    have hmono : a ^ (α - 1 + δ) ≤ (3 * S) ^ (α - 1 + δ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hfar.le (by linarith)
    have hS3 : (3 * S) ^ (α - 1 + δ) ≤ S ^ (α - 1 + δ) :=
      Real.rpow_le_rpow_of_nonpos hSd (by linarith) (by linarith)
    have hd0S : d0 ≤ S := by linarith
    have hSS : S * S ^ (α - 1 + δ) = S ^ (α + δ) := by
      have h := Real.rpow_add hSd 1 (α - 1 + δ)
      rw [Real.rpow_one] at h
      rw [show α + δ = 1 + (α - 1 + δ) by ring, h]
    calc a ^ α * (d0 * a⁻¹ * b⁻¹) ≤ a ^ α * (3 / 2 * d0 * a ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_left e1 (by positivity)
      _ = 3 / 2 * d0 * (a ^ (α - 1 + δ) * a ^ (-(1 + δ))) := by rw [← hexp]; ring
      _ ≤ 3 / 2 * S * (S ^ (α - 1 + δ) * a ^ (-(1 + δ))) := by
          have h0 : 0 ≤ a ^ (-(1 + δ)) := by positivity
          have hS' : 0 ≤ S ^ (α - 1 + δ) := by positivity
          refine mul_le_mul (mul_le_mul_of_nonneg_left hd0S (by norm_num)) (mul_le_mul_of_nonneg_right (hmono.trans hS3) h0)
            (by positivity) (by positivity)
      _ = 3 / 2 * S ^ (α + δ) * a ^ (-(1 + δ)) := by rw [← hSS]; ring
      _ ≤ _ := by
          have h0 : 0 ≤ a ^ (-(1 + δ)) := by positivity
          have h0' : 0 ≤ b ^ (-(1 + δ)) := by positivity
          nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (α + δ), mul_nonneg hSp h0, mul_nonneg hSp h0']


/-- The weighted envelope. -/
noncomputable def envG (α d l : ℝ) : ℝ :=
  (1 + |l|) ^ α * ((1 + |l|) ^ (-(2 : ℝ)) + (1 + |l - d|) ^ (-(2 : ℝ)) + |d| * (1 + |l|)⁻¹ * (1 + |l - d|)⁻¹)

theorem envG_nonneg (α d l : ℝ) : 0 ≤ envG α d l := by unfold envG; positivity

/-- **The weighted envelope integral.** -/
theorem env_integral {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hαδ : α + δ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ d : ℝ, Integrable (envG α d) ∧ ∫ l, envG α d l ≤ K * (1 + |d|) ^ (α + δ) := by
  have hα1 : α < 1 := by linarith
  have hr1 : 1 < 2 - α := by linarith
  have hr2 : 1 < 1 + δ := by linarith
  set c1 : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(2 - α)) with hc1
  set c2 : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(1 + δ)) with hc2
  have hc1n : 0 ≤ c1 := integral_nonneg fun x => by positivity
  have hc2n : 0 ≤ c2 := integral_nonneg fun x => by positivity
  set C3 : ℝ := 2 * 4 ^ (α + δ) + 2 with hC3
  have hC3n : 0 ≤ C3 := by positivity
  refine ⟨2 * c1 + 2 * C3 * c2, by positivity, fun d => ?_⟩
  set S : ℝ := 1 + |d| with hS
  have hS1 : 1 ≤ S := by have := abs_nonneg d; linarith
  have hSd : 0 < S := by linarith
  let M : ℝ → ℝ := fun l => (1 + |l|) ^ (-(2 - α)) + S ^ α * (1 + |l - d|) ^ (-(2 - α)) +
    C3 * S ^ (α + δ) * ((1 + |l|) ^ (-(1 + δ)) + (1 + |l - d|) ^ (-(1 + δ)))
  have hMi : Integrable M := by
    refine ((integrable_pow_decay hr1).add ((integrable_pow_decay_shift hr1 d).const_mul _)).add
      (((integrable_pow_decay hr2).add (integrable_pow_decay_shift hr2 d)).const_mul _)
  have hle : ∀ l, envG α d l ≤ M l := by
    intro l
    have ha : 1 ≤ 1 + |l| := by have := abs_nonneg l; linarith
    have hb : 1 ≤ 1 + |l - d| := by have := abs_nonneg (l - d); linarith
    have ha0 : 0 < 1 + |l| := by linarith
    have hb0 : 0 < 1 + |l - d| := by linarith
    have hab : 1 + |l| ≤ S * (1 + |l - d|) := one_add_abs_le_mul l d
    have e1 : (1 + |l|) ^ α * (1 + |l|) ^ (-(2 : ℝ)) = (1 + |l|) ^ (-(2 - α)) := by
      rw [← Real.rpow_add ha0]; congr 1; ring
    have e2 : (1 + |l|) ^ α * (1 + |l - d|) ^ (-(2 : ℝ)) ≤ S ^ α * (1 + |l - d|) ^ (-(2 - α)) := by
      have h1 : (1 + |l|) ^ α ≤ (S * (1 + |l - d|)) ^ α := Real.rpow_le_rpow ha0.le hab hα
      rw [Real.mul_rpow hSd.le hb0.le] at h1
      calc (1 + |l|) ^ α * (1 + |l - d|) ^ (-(2 : ℝ)) ≤ (S ^ α * (1 + |l - d|) ^ α) * (1 + |l - d|) ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = S ^ α * ((1 + |l - d|) ^ α * (1 + |l - d|) ^ (-(2 : ℝ))) := by ring
        _ = _ := by rw [← Real.rpow_add hb0]; congr 2; ring
    have hd1 : |d| ≤ |l| + |l - d| := by
      calc |d| = |l - (l - d)| := by ring_nf
        _ ≤ |l| + |l - d| := abs_sub _ _
    have hd2 : |l| ≤ |l - d| + |d| := by
      calc |l| = |(l - d) + d| := by ring_nf
        _ ≤ |l - d| + |d| := abs_add_le _ _
    have hd3 : |l - d| ≤ |l| + |d| := abs_sub _ _
    have e3 := cross_pointwise (α := α) (δ := δ) (a := 1 + |l|) (b := 1 + |l - d|) (d0 := |d|) hα hδ hαδ ha hb
      (abs_nonneg d) (by linarith) (by linarith) (by linarith)
    unfold envG
    calc _ = (1 + |l|) ^ α * (1 + |l|) ^ (-(2 : ℝ)) + (1 + |l|) ^ α * (1 + |l - d|) ^ (-(2 : ℝ)) +
          (1 + |l|) ^ α * (|d| * (1 + |l|)⁻¹ * (1 + |l - d|)⁻¹) := by ring
      _ ≤ _ := by
          rw [e1]
          have : (1 + |l|) ^ (-(2 - α)) + (1 + |l|) ^ α * (1 + |l - d|) ^ (-(2 : ℝ)) + (1 + |l|) ^ α * (|d| * (1 + |l|)⁻¹ * (1 + |l - d|)⁻¹) ≤
              (1 + |l|) ^ (-(2 - α)) + S ^ α * (1 + |l - d|) ^ (-(2 - α)) + C3 * S ^ (α + δ) *
                ((1 + |l|) ^ (-(1 + δ)) + (1 + |l - d|) ^ (-(1 + δ))) := add_le_add (add_le_add le_rfl e2) e3
          exact this
  have hI : Integrable (envG α d) := by
    refine hMi.mono' ?_ (Eventually.of_forall fun l => ?_)
    · unfold envG
      refine Continuous.aestronglyMeasurable ?_
      have : ∀ x : ℝ, 0 < 1 + |x| := fun x => by positivity
      refine Continuous.mul ?_ (Continuous.add (Continuous.add ?_ ?_) (Continuous.mul (Continuous.mul continuous_const ?_) ?_))
      · exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (this x).ne')
      · exact Continuous.rpow_const (by fun_prop) (fun x => Or.inl (this x).ne')
      · exact Continuous.rpow_const (by fun_prop : Continuous fun l : ℝ => 1 + |l - d|) (fun x => Or.inl (by positivity))
      · exact Continuous.inv₀ (by fun_prop) (fun x => (this x).ne')
      · exact Continuous.inv₀ (by fun_prop) (fun x => by positivity)
    · rw [Real.norm_of_nonneg (envG_nonneg α d l)]; exact hle l
  refine ⟨hI, ?_⟩
  calc ∫ l, envG α d l ≤ ∫ l, M l := integral_mono hI hMi hle
    _ = c1 + S ^ α * c1 + C3 * S ^ (α + δ) * (c2 + c2) := by
        have i1 : Integrable fun l : ℝ => (1 + |l|) ^ (-(2 - α)) := integrable_pow_decay hr1
        have i2 : Integrable fun l : ℝ => S ^ α * (1 + |l - d|) ^ (-(2 - α)) :=
          (integrable_pow_decay_shift hr1 d).const_mul _
        have i4 : Integrable fun l : ℝ => (1 + |l|) ^ (-(1 + δ)) := integrable_pow_decay hr2
        have i5 : Integrable fun l : ℝ => (1 + |l - d|) ^ (-(1 + δ)) := integrable_pow_decay_shift hr2 d
        have i3 : Integrable fun l : ℝ => C3 * S ^ (α + δ) * ((1 + |l|) ^ (-(1 + δ)) + (1 + |l - d|) ^ (-(1 + δ))) :=
          (i4.add i5).const_mul _
        have s1 := integral_add (f := fun l : ℝ => (1 + |l|) ^ (-(2 - α)) + S ^ α * (1 + |l - d|) ^ (-(2 - α)))
          (g := fun l : ℝ => C3 * S ^ (α + δ) * ((1 + |l|) ^ (-(1 + δ)) + (1 + |l - d|) ^ (-(1 + δ)))) (i1.add i2) i3
        have s2 := integral_add (f := fun l : ℝ => (1 + |l|) ^ (-(2 - α))) (g := fun l : ℝ => S ^ α * (1 + |l - d|) ^ (-(2 - α))) i1 i2
        have s3 := integral_add (f := fun l : ℝ => (1 + |l|) ^ (-(1 + δ))) (g := fun l : ℝ => (1 + |l - d|) ^ (-(1 + δ))) i4 i5
        have s4 := integral_const_mul (μ := volume) (S ^ α) (fun l : ℝ => (1 + |l - d|) ^ (-(2 - α)))
        have s5 := integral_const_mul (μ := volume) (C3 * S ^ (α + δ)) (fun l : ℝ => (1 + |l|) ^ (-(1 + δ)) + (1 + |l - d|) ^ (-(1 + δ)))
        have s6 := integral_pow_decay_shift (r := 2 - α) d
        have s7 := integral_pow_decay_shift (r := 1 + δ) d
        simp only [M]
        rw [s1, s2, s4, s5, s3, s6, s7]
    _ ≤ (2 * c1 + 2 * C3 * c2) * S ^ (α + δ) := by
        have h1 : S ^ α ≤ S ^ (α + δ) := Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
        have h2 : 1 ≤ S ^ (α + δ) := Real.one_le_rpow hS1 (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right h1 hc1n, mul_le_mul_of_nonneg_right h2 hc1n]

end WaveTurbulence.VineEstS5C.P4.W2.K2
