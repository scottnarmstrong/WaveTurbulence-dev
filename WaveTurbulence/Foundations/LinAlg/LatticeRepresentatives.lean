/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.FiniteRepresentatives
public import WaveTurbulence.Foundations.LinAlg.LatticeObservations

/-!
# Finite representatives on the square lattice

The representative conclusion of TARGET Lemma A.6 (`finitelem`, L2435–L2445).
The first theorem retains the exact finite-set count; the polynomial estimate
then absorbs constants under the ambient large-box convention `2 ≤ L ≤ M`.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset Module
open scoped Classical InnerProductSpace

/-- A finite set of lattice representatives with the exact record-count bound. -/
theorem exists_lattice_representatives_card {d : ℕ} {L M : ℝ} (hL : 0 < L) :
    ∃ R : Finset (Mom d),
      (∀ k ∈ R, ∃ n : Fin d → ℤ, k = latticePoint L n) ∧
      R.card ≤ ∑ q : Fin (d + 1),
        ((latticeTestBall d L M).card * (latticeObservationValues L M).card) ^ q.val ∧
      ∀ k : Fin d → ℤ, ∃ k' ∈ R, ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
        (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M ↔
          |⟪k', latticePoint L z⟫_ℝ| ≤ M) ∧
        (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M →
          ⟪latticePoint L k, latticePoint L z⟫_ℝ = ⟪k', latticePoint L z⟫_ℝ) := by
  let ℓ : (Fin d → ℤ) → Mom d →ₗ[ℝ] ℝ :=
    fun k => (innerSL ℝ (latticePoint L k)).toLinearMap
  obtain ⟨R, hcard, hR⟩ := exists_finite_linear_representatives
    (latticeTestBall d L M) (latticeObservationValues L M) ℓ
  refine ⟨R.image (latticePoint L), ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨n, _, rfl⟩ := mem_image.mp hk
    exact ⟨n, rfl⟩
  · apply card_image_le.trans
    rw [show finrank ℝ (Mom d) = d by simp [Mom]] at hcard
    exact hcard
  intro k
  obtain ⟨k', hk', hrep⟩ := hR k
  refine ⟨latticePoint L k', mem_image.mpr ⟨k', hk', rfl⟩, ?_⟩
  intro z hz
  have h := hrep (latticePoint L z) (latticePoint_mem_testBall hL z hz)
  change (⟪latticePoint L k, latticePoint L z⟫_ℝ ∈ latticeObservationValues L M ↔
      ⟪latticePoint L k', latticePoint L z⟫_ℝ ∈ latticeObservationValues L M) ∧
    (⟪latticePoint L k, latticePoint L z⟫_ℝ ∈ latticeObservationValues L M →
      ⟪latticePoint L k, latticePoint L z⟫_ℝ =
        ⟪latticePoint L k', latticePoint L z⟫_ℝ) at h
  simpa only [inner_mem_latticeObservationValues_iff hL] using h

/-- Absorb the number of possible record lengths into a power of `M`. -/
lemma nat_succ_le_pow_of_two_le {M : ℝ} (hM : 2 ≤ M) (d : ℕ) :
    (d + 1 : ℝ) ≤ M ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    push_cast
    have hp : 0 ≤ M ^ d := pow_nonneg (by linarith) _
    nlinarith

/-- The coordinate-box bound is polynomial in `M`, uniformly for `L ≤ M`. -/
lemma lattice_box_bound {L M : ℝ} (hM : 2 ≤ M) (hLM : L ≤ M) :
    2 * (L * M) + 3 ≤ M ^ 4 := by
  have hM0 : 0 ≤ M := by linarith
  have hmul := mul_le_mul_of_nonneg_right hLM hM0
  have hs : 4 ≤ M ^ 2 := by nlinarith
  nlinarith [sq_nonneg (M ^ 2 - 2)]

/-- The inner-product value enumeration is polynomial in `M`. -/
lemma lattice_value_bound {L M : ℝ} (hM : 2 ≤ M) (hL : 0 ≤ L) (hLM : L ≤ M) :
    2 * (L ^ 2 * M) + 3 ≤ M ^ 5 := by
  have hM0 : 0 ≤ M := by linarith
  have hs : 4 ≤ M ^ 2 := by nlinarith
  have hl2 : L ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hL hLM 2
  have hl3 := mul_le_mul_of_nonneg_right hl2 hM0
  have hm3 : 8 ≤ M ^ 3 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hs (pow_nonneg hM0 3)
  nlinarith

/-- TARGET Lemma A.6, representative conclusion. Under `2 ≤ L ≤ M`,
`M^(4d²+6d)` representatives suffice. The large-`L` convention permits the
source's coefficient-one polynomial count; its literal endpoint `M=L=1`
would incorrectly require at most one representative. -/
theorem exists_lattice_representatives {d : ℕ} {L M : ℝ}
    (hL : 2 ≤ L) (hLM : L ≤ M) :
    ∃ R : Finset (Mom d),
      (∀ k ∈ R, ∃ n : Fin d → ℤ, k = latticePoint L n) ∧
      (R.card : ℝ) ≤ M ^ (4 * d * d + 6 * d) ∧
      ∀ k : Fin d → ℤ, ∃ k' ∈ R, ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
        (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M ↔
          |⟪k', latticePoint L z⟫_ℝ| ≤ M) ∧
        (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M →
          ⟪latticePoint L k, latticePoint L z⟫_ℝ = ⟪k', latticePoint L z⟫_ℝ) := by
  have hM : 2 ≤ M := hL.trans hLM
  have hM0 : 0 ≤ M := by linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨R, hRl, hcard, hrep⟩ := exists_lattice_representatives_card
    (d := d) (M := M) (by linarith : 0 < L)
  refine ⟨R, hRl, ?_, hrep⟩
  have hS : ((latticeTestBall d L M).card : ℝ) ≤ M ^ (4 * d) := by
    calc
      _ ≤ (2 * (L * M) + 3) ^ d := card_latticeTestBall_le (mul_nonneg hL0 hM0)
      _ ≤ (M ^ 4) ^ d := pow_le_pow_left₀ (by positivity) (lattice_box_bound hM hLM) d
      _ = _ := by rw [← pow_mul]
  have hY : ((latticeObservationValues L M).card : ℝ) ≤ M ^ 5 :=
    (card_latticeObservationValues_le (mul_nonneg (sq_nonneg L) hM0)).trans
      (lattice_value_bound hM hL0 hLM)
  have hSY : (((latticeTestBall d L M).card *
      (latticeObservationValues L M).card : ℕ) : ℝ) ≤ M ^ (4 * d + 5) := by
    rw [Nat.cast_mul, pow_add]
    exact mul_le_mul hS hY (by positivity) (by positivity)
  calc
    (R.card : ℝ) ≤ ∑ q : Fin (d + 1),
        (((latticeTestBall d L M).card * (latticeObservationValues L M).card : ℕ) : ℝ) ^ q.val := by
      exact_mod_cast hcard
    _ ≤ ∑ _q : Fin (d + 1), M ^ ((4 * d + 5) * d) := by
      apply sum_le_sum
      intro q _
      calc
        _ ≤ (M ^ (4 * d + 5)) ^ q.val := pow_le_pow_left₀ (by positivity) hSY _
        _ = M ^ ((4 * d + 5) * q.val) := (pow_mul _ _ _).symm
        _ ≤ _ := pow_le_pow_right₀ (by linarith : 1 ≤ M)
          (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ q.isLt))
    _ = (d + 1 : ℝ) * M ^ ((4 * d + 5) * d) := by simp
    _ ≤ M ^ d * M ^ ((4 * d + 5) * d) :=
      mul_le_mul_of_nonneg_right (nat_succ_le_pow_of_two_le hM d) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end WaveTurbulence.LinAlg
