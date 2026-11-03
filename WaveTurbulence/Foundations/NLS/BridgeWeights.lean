/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NLS.AkClass

/-!
# Weight comparisons for the NLS reduction bridge

TARGET L540–L566: the Euclidean Japanese bracket and the integer sup-norm
rapid-decay convention describe the same coefficient class.
-/

public section

noncomputable section

open Set

namespace WaveTurbulence.NLS

variable {d : ℕ}

/-- Rewrite a real Japanese-bracket power in the squared-bracket convention. -/
theorem bridge_sqrt_rpow (x s : ℝ) (hx : 0 ≤ x) :
    Real.sqrt x ^ s = x ^ (s / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  congr 1
  ring

/-- Rapid integer decay controls every real momentum weight uniformly in an arbitrary time set. -/
theorem bridge_uniform_weight_bound {L : ℝ} (hL : 0 < L) {S : Set ℝ}
    {a : ℝ → (Fin d → ℤ) → ℂ}
    (ha : ∀ N : ℕ, ∃ C, ∀ t ∈ S, ∀ n, ‖a t n‖ ≤ C * (1 + ‖n‖) ^ (-(N : ℤ)))
    (s : ℝ) : ∃ B, ∀ t ∈ S, ∀ n, Real.sqrt (1 + ‖latticePoint L n‖ ^ 2) ^ s * ‖a t n‖ ≤ B := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s / 2)
  obtain ⟨C, hC⟩ := ha (2 * N)
  let A : ℝ := 1 + d / L ^ 2
  refine ⟨A ^ N * C, fun t ht n => ?_⟩
  have hw : Real.sqrt (1 + ‖latticePoint L n‖ ^ 2) ^ s ≤ A ^ N * (1 + ‖n‖) ^ (2 * N) := by
    rw [bridge_sqrt_rpow _ _ (by positivity)]
    calc
      _ ≤ (1 + ‖latticePoint L n‖ ^ 2) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _)) hN
      _ = (1 + ‖latticePoint L n‖ ^ 2) ^ N := Real.rpow_natCast _ _
      _ ≤ (A * (1 + ‖n‖) ^ 2) ^ N :=
        pow_le_pow_left₀ (by positivity) (one_add_norm_latticePoint_sq_le hL n) N
      _ = _ := by rw [mul_pow, ← pow_mul]
  apply (mul_le_mul hw (hC t ht n) (norm_nonneg _) (by dsimp [A]; positivity)).trans_eq
  rw [zpow_neg, zpow_natCast]
  have hp : (1 + ‖n‖) ^ (2 * N) ≠ 0 := by positivity
  field_simp

/-- Real Japanese-bracket bounds imply the landed rapid-decay predicate. -/
theorem bridge_isRapidDecay_of_weight_bounds {L : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ}
    (hc : ∀ s : ℝ, ∃ C, ∀ n, Real.sqrt (1 + ‖latticePoint L n‖ ^ 2) ^ s * ‖c n‖ ≤ C) :
    IsRapidDecay c := by
  intro N
  obtain ⟨C, hC⟩ := hc N
  let K := Real.sqrt (2 * max 1 (L ^ 2))
  refine ⟨K ^ N * C, fun n => ?_⟩
  have hb : 1 + ‖n‖ ≤ K * Real.sqrt (1 + ‖latticePoint L n‖ ^ 2) := by
    have H := Real.sqrt_le_sqrt (one_add_norm_sq_le_japanese hL n)
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 1 + ‖n‖),
      Real.sqrt_mul (by positivity : 0 ≤ 2 * max 1 (L ^ 2)), K] using H
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ ‖c n‖ * (K * Real.sqrt (1 + ‖latticePoint L n‖ ^ 2)) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb N) (norm_nonneg _)
    _ = K ^ N * (Real.sqrt (1 + ‖latticePoint L n‖ ^ 2) ^ (N : ℝ) * ‖c n‖) := by
      rw [Real.rpow_natCast, mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hC n) (by dsimp [K]; positivity)

end WaveTurbulence.NLS
