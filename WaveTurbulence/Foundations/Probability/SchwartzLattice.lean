/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Torus.Inversion
public import WaveTurbulence.Foundations.LinAlg.LatticeRescaling
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Square roots of Schwartz envelopes on the lattice

The deterministic decay input for TARGET's random initial data. Smoothness of
the square root is unnecessary: only its rapid decay on the discrete lattice
is used. Lean's real square root also makes the bound valid without a sign
hypothesis on the Schwartz envelope.
-/

public section

namespace WaveTurbulence.Probability
open Finset
open scoped Classical SchwartzMap

/-- A Schwartz function is uniformly bounded after any polynomial weight. -/
theorem schwartz_one_add_norm_bound {d : ℕ} (φ : 𝓢(Mom d, ℝ)) (N : ℕ) :
    ∃ C ≥ 0, ∀ x, (1 + ‖x‖) ^ N * |φ x| ≤ C := by
  let C := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) φ
  refine ⟨C, by positivity, ?_⟩
  intro x
  simpa using (SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl φ x)

/-- The square root of a Schwartz envelope decays against any polynomial weight. -/
theorem sqrt_schwartz_one_add_norm_bound {d : ℕ} (φ : 𝓢(Mom d, ℝ)) (N : ℕ) :
    ∃ C ≥ 0, ∀ x, (1 + ‖x‖) ^ N * Real.sqrt (φ x) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := schwartz_one_add_norm_bound φ (2 * N)
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro x
  have h := Real.sqrt_le_sqrt (hbound x)
  have heq : (1 + ‖x‖) ^ (2 * N) = ((1 + ‖x‖) ^ N) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm N 2]
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_abs_self _)) (by positivity)).trans h

/-- Integer sup norm is controlled by the rescaled Euclidean momentum norm. -/
theorem norm_integer_le_lattice {d : ℕ} {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) :
    ‖n‖ ≤ L * ‖latticePoint L n‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hL.le (norm_nonneg _))).mpr
  intro i
  have h : ‖(n i : ℝ) / L‖ ≤ ‖latticePoint L n‖ := PiLp.norm_apply_le (latticePoint L n) i
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hL] at h
  simpa only [Int.norm_eq_abs, mul_comm] using (div_le_iff₀ hL).mp h

/-- Sampling the square root of a Schwartz function gives a rapidly decaying
coefficient family on the lattice. -/
theorem isRapidDecay_sqrt_schwartz {d : ℕ} {L : ℝ} (hL : 0 < L)
    (φ : 𝓢(Mom d, ℝ)) :
    IsRapidDecay (fun n => (Real.sqrt (φ (latticePoint L n)) : ℂ)) := by
  intro N
  obtain ⟨C, hC, hbound⟩ := sqrt_schwartz_one_add_norm_bound φ N
  let K : ℝ := max 1 L
  have hK : 0 ≤ K := le_trans zero_le_one (le_max_left _ _)
  refine ⟨K ^ N * C, ?_⟩
  intro n
  have hbase : 1 + ‖n‖ ≤ K * (1 + ‖latticePoint L n‖) := by
    have hn := norm_integer_le_lattice hL n
    have h1 : 1 ≤ K := le_max_left _ _
    have hLK : L ≤ K := le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_right hLK (norm_nonneg (latticePoint L n))]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖n‖) hbase N
  rw [mul_pow] at hpow
  have hmul : Real.sqrt (φ (latticePoint L n)) * (1 + ‖n‖) ^ N ≤ K ^ N * C := by
    calc
      _ ≤ Real.sqrt (φ (latticePoint L n)) * (K ^ N * (1 + ‖latticePoint L n‖) ^ N) :=
        mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)
      _ = K ^ N * ((1 + ‖latticePoint L n‖) ^ N * Real.sqrt (φ (latticePoint L n))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hbound _) (pow_nonneg hK N)
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), zpow_neg, zpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖n‖) N)]
  exact hmul

end WaveTurbulence.Probability
