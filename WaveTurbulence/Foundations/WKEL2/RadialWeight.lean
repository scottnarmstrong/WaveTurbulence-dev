/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WKEL2.Polar
public import WaveTurbulence.Frozen.Defs.Mom
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Finiteness of the radial weight A_k

The radial weight in §2 of `docs/research/git20-general-d.md`. Finiteness is
reduced by a Peetre inequality to radial integration in dimension `d-2`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace WaveTurbulence.WKEL2

variable {d : ℕ}

/-- The radial weight `A_k(θ)` of the general-dimensional estimate. -/
@[expose] def radialWeight (d : ℕ) (s : ℝ) (k θ : Mom d) : ℝ :=
  ∫ ρ in Ioi (0 : ℝ), (1 + ‖k + ρ • θ‖ ^ 2) ^ (-s) * ρ ^ (d - 3)

/-- A scalar Peetre inequality, kept separate from transcendental expressions. -/
theorem one_add_sq_peetre {r K N : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hN : 0 ≤ N)
    (h : r ≤ K + N) : 1 + r ^ 2 ≤ (2 * (1 + K ^ 2)) * (1 + N ^ 2) := by
  have hs : r ^ 2 ≤ (K + N) ^ 2 := (sq_le_sq₀ hr (add_nonneg hK hN)).mpr h
  nlinarith only [hs, sq_nonneg (K - N), sq_nonneg K, sq_nonneg N,
    mul_nonneg (sq_nonneg K) (sq_nonneg N)]

/-- Transfer a negative power through a multiplicative Peetre bound. -/
theorem rpow_neg_le_of_le_mul {x y C s : ℝ} (hx : 0 < x) (hy : 0 < y) (hC : 0 < C)
    (hs : 0 ≤ s) (h : x ≤ C * y) : y ^ (-s) ≤ C ^ s * x ^ (-s) := by
  have ht := Real.rpow_le_rpow_of_nonpos hx h (neg_nonpos.mpr hs)
  calc
    y ^ (-s) = C ^ s * (C * y) ^ (-s) := by
      rw [Real.mul_rpow hC.le hy.le, ← mul_assoc, ← Real.rpow_add hC,
        add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.rpow_nonneg hC.le s)

/-- The centered radial weight is integrable exactly in the required open range. -/
theorem integrable_centered_radialWeight (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) :
    IntegrableOn (fun ρ : ℝ => (1 + ρ ^ 2) ^ (-s) * ρ ^ (d - 3)) (Ioi 0) := by
  have : Nontrivial (Mom (d - 2)) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  have hdim : (Module.finrank ℝ (Mom (d - 2)) : ℝ) < 2 * s := by
    rw [finrank_euclideanSpace_fin, Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
    linarith only [hs]
  have hi : Integrable (fun x : Mom (d - 2) => (1 + ‖x‖ ^ 2) ^ (-s)) := by
    have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure (Mom (d - 2)))) hdim
    simpa only [show -(2 * s) / 2 = -s by ring] using h
  have hr := (integrable_fun_norm_addHaar (volume : Measure (Mom (d - 2)))
    (f := fun ρ : ℝ => (1 + ρ ^ 2) ^ (-s))).mp hi
  simpa only [finrank_euclideanSpace_fin, show d - 2 - 1 = d - 3 by omega,
    smul_eq_mul, mul_comm] using hr

/-- Finiteness of `A_k(θ)` in Lemma 3: no Bochner default value is used. -/
theorem integrable_radialWeight (hd : 3 ≤ d) (s : ℝ)
    (hs : (d : ℝ) / 2 - 1 < s) (k θ : Mom d) (hθ : ‖θ‖ = 1) :
    IntegrableOn (fun ρ : ℝ => (1 + ‖k + ρ • θ‖ ^ 2) ^ (-s) * ρ ^ (d - 3)) (Ioi 0) := by
  have hs0 : 0 ≤ s := by
    have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith only [hs, hdR]
  let C : ℝ := (2 * (1 + ‖k‖ ^ 2)) ^ s
  have hi := (integrable_centered_radialWeight hd s hs).const_mul C
  refine hi.mono' ?_ ?_
  · have hbase : Continuous (fun ρ : ℝ => 1 + ‖k + ρ • θ‖ ^ 2) := by fun_prop
    exact ((hbase.rpow_const (fun _ => Or.inl (by positivity))).mul
      (continuous_id.pow _)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ρ hρ
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hρ.le _))]
    have ht : ρ ≤ ‖k‖ + ‖k + ρ • θ‖ := by
      have h := norm_sub_le (k + ρ • θ) k
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le, hθ, mul_one] at h
      exact h.trans_eq (add_comm _ _)
    have hb := one_add_sq_peetre hρ.le (norm_nonneg k) (norm_nonneg _) ht
    have hw := rpow_neg_le_of_le_mul (by positivity : 0 < 1 + ρ ^ 2)
      (by positivity : 0 < 1 + ‖k + ρ • θ‖ ^ 2) (by positivity) hs0 hb
    exact (mul_le_mul_of_nonneg_right hw (pow_nonneg hρ.le _)).trans_eq (by ring)

/-- The radial weight is nonnegative whenever its defining integral is evaluated. -/
theorem radialWeight_nonneg (d : ℕ) (s : ℝ) (k θ : Mom d) :
    0 ≤ radialWeight d s k θ := by
  exact setIntegral_nonneg measurableSet_Ioi fun ρ hρ =>
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg hρ.le _)

end WaveTurbulence.WKEL2
