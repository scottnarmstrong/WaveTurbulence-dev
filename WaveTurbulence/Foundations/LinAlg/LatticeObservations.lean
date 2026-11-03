/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.LatticePoint

/-!
# Finite lattice observations

Finite sets of lattice tests and their bounded inner-product values, for
TARGET Lemma A.6 (`finitelem`, L2435–L2445). Integer ceilings are used only to
enumerate supersets; the final filters retain the exact Euclidean thresholds.
-/

public section

namespace WaveTurbulence.LinAlg
open Finset
open scoped Classical InnerProductSpace

/-- An integer coordinate box containing the Euclidean ball of radius `B`. -/
@[expose] noncomputable def integerCoordinateBox (d : ℕ) (B : ℝ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ => Icc (-⌈B⌉) ⌈B⌉)

/-- The exact finite set of lattice points in the closed ball of radius `M`. -/
@[expose] noncomputable def latticeTestBall (d : ℕ) (L M : ℝ) : Finset (Mom d) :=
  ((integerCoordinateBox d (L * M)).image (latticePoint L)).filter (fun z => ‖z‖ ≤ M)

/-- The exact bounded values on the lattice of inner products. -/
@[expose] noncomputable def latticeObservationValues (L M : ℝ) : Finset ℝ :=
  ((Icc (-⌈L ^ 2 * M⌉) ⌈L ^ 2 * M⌉).image (fun a : ℤ => (a : ℝ) / L ^ 2)).filter
    (fun y => |y| ≤ M)

/-- An absolute-value bound places an integer inside the ceiling interval. -/
theorem mem_integer_interval_of_abs_le {a : ℤ} {B : ℝ} (ha : |(a : ℝ)| ≤ B) :
    a ∈ Icc (-⌈B⌉) ⌈B⌉ := by
  have hb := Int.le_ceil B
  apply mem_Icc.mpr
  constructor
  · have : (-⌈B⌉ : ℤ) ≤ a := by
      exact_mod_cast (show (-(⌈B⌉ : ℝ)) ≤ (a : ℝ) by linarith [neg_abs_le (a : ℝ)])
    exact this
  · exact_mod_cast (show (a : ℝ) ≤ (⌈B⌉ : ℝ) by linarith [le_abs_self (a : ℝ)])

/-- Bounded lattice points belong to the finite test set. -/
theorem latticePoint_mem_testBall {d : ℕ} {L M : ℝ} (hL : 0 < L)
    (z : Fin d → ℤ) (hz : ‖latticePoint L z‖ ≤ M) :
    latticePoint L z ∈ latticeTestBall d L M := by
  apply mem_filter.mpr
  refine ⟨mem_image.mpr ⟨z, ?_, rfl⟩, hz⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  apply mem_integer_interval_of_abs_le
  have hc := (PiLp.norm_apply_le (latticePoint L z) j).trans hz
  simp only [latticePoint, Real.norm_eq_abs, abs_div,
    abs_of_pos hL] at hc
  have hmul := (div_le_iff₀ hL).mp hc
  simpa only [mul_comm] using hmul

/-- The integer enumeration interval has at most `2B+3` elements. -/
theorem card_integer_interval_le {B : ℝ} (hB : 0 ≤ B) :
    ((Icc (-⌈B⌉) ⌈B⌉ : Finset ℤ).card : ℝ) ≤ 2 * B + 3 := by
  have hceil : 0 ≤ ⌈B⌉ := Int.ceil_nonneg hB
  have hcard := Int.card_Icc_of_le (a := -⌈B⌉) (b := ⌈B⌉) (by omega)
  have heq : ((Icc (-⌈B⌉) ⌈B⌉ : Finset ℤ).card : ℝ) = 2 * (⌈B⌉ : ℝ) + 1 := by
    exact_mod_cast (show ((Icc (-⌈B⌉) ⌈B⌉ : Finset ℤ).card : ℤ) = 2 * ⌈B⌉ + 1 by omega)
  rw [heq]
  linarith [Int.ceil_lt_add_one B]

/-- A coordinate box has the expected product cardinality. -/
theorem card_integerCoordinateBox (d : ℕ) (B : ℝ) :
    (integerCoordinateBox d B).card = (Icc (-⌈B⌉) ⌈B⌉ : Finset ℤ).card ^ d := by
  simp [integerCoordinateBox, Fintype.card_piFinset]

/-- The square-torus inner product is an integer divided by `L²`. -/
theorem inner_latticePoint {d : ℕ} (L : ℝ) (k z : Fin d → ℤ) :
    ⟪latticePoint L k, latticePoint L z⟫_ℝ =
      ((∑ i, k i * z i : ℤ) : ℝ) / L ^ 2 := by
  simp only [latticePoint, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, Int.cast_sum, Int.cast_mul]
  simp only [div_mul_div_comm, ← Finset.sum_div, pow_two, mul_comm]

/-- The value filter retains precisely the source inner-product threshold. -/
theorem inner_mem_latticeObservationValues_iff {d : ℕ} {L M : ℝ} (hL : 0 < L)
    (k z : Fin d → ℤ) :
    ⟪latticePoint L k, latticePoint L z⟫_ℝ ∈ latticeObservationValues L M ↔
      |⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M := by
  constructor
  · intro h
    exact (mem_filter.mp h).2
  intro h
  apply mem_filter.mpr
  refine ⟨?_, h⟩
  refine mem_image.mpr ⟨∑ i, k i * z i, ?_, (inner_latticePoint L k z).symm⟩
  apply mem_integer_interval_of_abs_le
  rw [inner_latticePoint, abs_div, abs_of_pos (sq_pos_of_pos hL)] at h
  have hh := (div_le_iff₀ (sq_pos_of_pos hL)).mp h
  simpa only [mul_comm] using hh

/-- A real-coordinate cardinality bound for the exact lattice test ball. -/
theorem card_latticeTestBall_le {d : ℕ} {L M : ℝ} (hLM : 0 ≤ L * M) :
    ((latticeTestBall d L M).card : ℝ) ≤ (2 * (L * M) + 3) ^ d := by
  have hc : (latticeTestBall d L M).card ≤ (integerCoordinateBox d (L * M)).card :=
    (card_filter_le _ _).trans card_image_le
  calc
    _ ≤ ((integerCoordinateBox d (L * M)).card : ℝ) := by exact_mod_cast hc
    _ = ((Icc (-⌈L * M⌉) ⌈L * M⌉ : Finset ℤ).card : ℝ) ^ d := by
      rw [card_integerCoordinateBox, Nat.cast_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (card_integer_interval_le hLM) d

/-- A real-coordinate cardinality bound for the exact lattice value set. -/
theorem card_latticeObservationValues_le {L M : ℝ} (hLM : 0 ≤ L ^ 2 * M) :
    ((latticeObservationValues L M).card : ℝ) ≤ 2 * (L ^ 2 * M) + 3 := by
  have hc : (latticeObservationValues L M).card ≤
      (Icc (-⌈L ^ 2 * M⌉) ⌈L ^ 2 * M⌉ : Finset ℤ).card :=
    (card_filter_le _ _).trans card_image_le
  exact (show ((latticeObservationValues L M).card : ℝ) ≤
    ((Icc (-⌈L ^ 2 * M⌉) ⌈L ^ 2 * M⌉ : Finset ℤ).card : ℝ) by exact_mod_cast hc).trans
      (card_integer_interval_le hLM)

end WaveTurbulence.LinAlg
