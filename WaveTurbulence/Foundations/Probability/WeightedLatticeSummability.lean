/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Inversion
public import WaveTurbulence.Foundations.LinAlg.LatticeRescaling

/-!
# Summability with every real momentum weight

A rapidly decaying lattice family is summable against `⟨k⟩^s` for every real `s`,
where the campaign's Japanese-bracket convention is `(1+‖k‖²)^(s/2)`.
-/

public section

namespace WaveTurbulence.Probability
open Finset
open scoped Classical

/-- Euclidean momentum norm is bounded by the integer-coordinate sup norm. -/
theorem norm_lattice_le_integer {d : ℕ} {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    ‖latticePoint L n‖ ≤ (d : ℝ) / L * ‖n‖ := by
  calc
    _ ≤ ∑ i, |latticePoint L n i| := LinAlg.norm_mom_le_sum_abs _
    _ ≤ ∑ _i : Fin d, ‖n‖ / L := by
      apply sum_le_sum
      intro i _
      simp only [latticePoint, abs_div, abs_of_pos hL]
      exact div_le_div_of_nonneg_right (by simpa only [Int.norm_eq_abs] using norm_le_pi_norm n i) hL.le
    _ = _ := by simp; ring

/-- Rapid decay implies absolute summability with any real Japanese-bracket weight. -/
theorem summable_real_weight_of_isRapidDecay {d : ℕ} {L : ℝ} (hL : 0 < L)
    {c : (Fin d → ℤ) → ℂ} (hc : IsRapidDecay c) (s : ℝ) :
    Summable (fun n => (1 + ‖latticePoint L n‖ ^ 2) ^ (s / 2) * ‖c n‖) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (s / 2)
  let C : ℝ := (d : ℝ) / L
  let A : ℝ := 1 + C ^ 2
  have hC : 0 ≤ C := div_nonneg (Nat.cast_nonneg _) hL.le
  have hA : 0 ≤ A := by positivity
  have hb (n : Fin d → ℤ) : 1 + ‖latticePoint L n‖ ^ 2 ≤ A * (1 + ‖n‖) ^ 2 := by
    have hk := pow_le_pow_left₀ (norm_nonneg (latticePoint L n)) (norm_lattice_le_integer hL n) 2
    change ‖latticePoint L n‖ ^ 2 ≤ (C * ‖n‖) ^ 2 at hk
    dsimp only [A]
    nlinarith [norm_nonneg n, sq_nonneg C, sq_nonneg ‖n‖,
      mul_nonneg (sq_nonneg C) (norm_nonneg n)]
  have hw (n : Fin d → ℤ) :
      (1 + ‖latticePoint L n‖ ^ 2) ^ (s / 2) ≤ A ^ N * (1 + ‖n‖) ^ (2 * N) := by
    calc
      _ ≤ (1 + ‖latticePoint L n‖ ^ 2) ^ (N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖latticePoint L n‖]) hN
      _ = (1 + ‖latticePoint L n‖ ^ 2) ^ N := Real.rpow_natCast _ _
      _ ≤ (A * (1 + ‖n‖) ^ 2) ^ N := pow_le_pow_left₀ (by positivity) (hb n) N
      _ = _ := by rw [mul_pow, ← pow_mul]
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((hc.summable_norm_mul_pow (2 * N)).mul_left (A ^ N))
  calc
    _ ≤ (A ^ N * (1 + ‖n‖) ^ (2 * N)) * ‖c n‖ :=
      mul_le_mul_of_nonneg_right (hw n) (norm_nonneg _)
    _ = _ := by ring

end WaveTurbulence.Probability
