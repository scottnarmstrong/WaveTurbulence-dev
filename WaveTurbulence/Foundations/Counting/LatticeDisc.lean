/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleArc
public import WaveTurbulence.Foundations.NumberTheory.Sawtooth
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Exact finite lattice discs and vertical slicing

NT-CIRCLE-v2 goal 2: the center has the Euclidean carrier, lattice points
have carrier `Fin 2 → ℤ`, and the closed boundary is included. The finite
description is by vertical integer intervals, with a proved membership
characterization by Euclidean distance. No discrepancy estimate is asserted.
-/

public section

namespace WaveTurbulence.Counting

/-- The finite set of integers in a closed real interval. -/
@[expose] noncomputable def integerInterval (l u : ℝ) : Finset ℤ :=
  Finset.Icc ⌈l⌉ ⌊u⌋

@[simp] theorem mem_integerInterval (n : ℤ) (l u : ℝ) :
    n ∈ integerInterval l u ↔ l ≤ (n : ℝ) ∧ (n : ℝ) ≤ u := by
  simp only [integerInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor]

/-- Exact counting of a closed interval, including both integer endpoints. -/
theorem card_integerInterval_eq_sawtooth {l u : ℝ} (h : l ≤ u) :
    ((integerInterval l u).card : ℝ) =
      u - l - NumberTheory.sawtooth u - NumberTheory.sawtooth (-l) := by
  have hle : ⌈l⌉ ≤ ⌊u⌋ + 1 :=
    (Int.ceil_mono h).trans (Int.ceil_le_floor_add_one u)
  have hc := Int.card_Icc_of_le ⌈l⌉ ⌊u⌋ hle
  have hceil : ⌈l⌉ = -⌊-l⌋ := by
    simpa only [neg_neg] using (Int.ceil_neg (a := -l))
  change ((Finset.Icc ⌈l⌉ ⌊u⌋).card : ℝ) = _
  have hcR : ((Finset.Icc ⌈l⌉ ⌊u⌋).card : ℝ) = (⌊u⌋ : ℝ) + 1 - (⌈l⌉ : ℝ) := by
    exact_mod_cast hc
  rw [hcR, hceil, Int.cast_neg, NumberTheory.sawtooth_eq, NumberTheory.sawtooth_eq]
  ring

/-- Inserting a vertical integer coordinate into a specified column. -/
@[expose] def columnEmbedding (x : ℤ) : ℤ ↪ (Fin 2 → ℤ) where
  toFun y := ![x, y]
  inj' := by
    intro y z hyz
    exact congrFun hyz 1

/-- The integer points in a closed disc, enumerated by its vertical slices. -/
@[expose] noncomputable def latticeDisc (c : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    Finset (Fin 2 → ℤ) := by
  classical
  exact (integerInterval (c 0 - R) (c 0 + R)).biUnion fun x =>
    (integerInterval (c 1 - circleHeight R (c 0) x)
      (c 1 + circleHeight R (c 0) x)).map (columnEmbedding x)

/-- Real Euclidean realization of an integer point. -/
@[expose] noncomputable def latticePoint (n : Fin 2 → ℤ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i => (n i : ℝ)

theorem mem_latticeDisc_iff_intervals (n : Fin 2 → ℤ) (c : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    n ∈ latticeDisc c R ↔
      (n 0) ∈ integerInterval (c 0 - R) (c 0 + R) ∧
      (n 1) ∈ integerInterval (c 1 - circleHeight R (c 0) (n 0))
        (c 1 + circleHeight R (c 0) (n 0)) := by
  classical
  simp only [latticeDisc, Finset.mem_biUnion, Finset.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, heq⟩
    have hx0 : x = n 0 := congrFun heq 0
    have hy1 : y = n 1 := congrFun heq 1
    subst x
    subst y
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    refine ⟨n 0, hx, n 1, hy, ?_⟩
    ext i
    fin_cases i <;> rfl

private theorem sum_sq_le_iff {x y R : ℝ} (hR : 0 ≤ R) :
    x ^ 2 + y ^ 2 ≤ R ^ 2 ↔
      |x| ≤ R ∧ |y| ≤ Real.sqrt (R ^ 2 - x ^ 2) := by
  constructor
  · intro h
    have hx : x ^ 2 ≤ R ^ 2 := by linarith only [h, sq_nonneg y]
    have hs := Real.sq_sqrt (sub_nonneg.mpr hx)
    constructor
    · apply (sq_le_sq₀ (abs_nonneg x) hR).mp
      simpa only [sq_abs] using hx
    · apply (sq_le_sq₀ (abs_nonneg y) (Real.sqrt_nonneg _)).mp
      simp only [sq_abs]
      linarith only [h, hs]
  · rintro ⟨hx, hy⟩
    have hx2 := (sq_le_sq₀ (abs_nonneg x) hR).mpr hx
    have hy2 := (sq_le_sq₀ (abs_nonneg y) (Real.sqrt_nonneg _)).mpr hy
    simp only [sq_abs] at hx2 hy2
    have hs := Real.sq_sqrt (sub_nonneg.mpr hx2)
    linarith only [hy2, hs]

/-- The enumeration includes exactly the integer points of the closed
Euclidean disc, for an arbitrary real center and nonnegative radius. -/
theorem mem_latticeDisc {n : Fin 2 → ℤ} {c : EuclideanSpace ℝ (Fin 2)} {R : ℝ}
    (hR : 0 ≤ R) : n ∈ latticeDisc c R ↔ ‖latticePoint n - c‖ ≤ R := by
  have hnorm : ‖latticePoint n - c‖ ^ 2 =
      ((n 0 : ℝ) - c 0) ^ 2 + ((n 1 : ℝ) - c 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [latticePoint, Fin.sum_univ_two]
  rw [← sq_le_sq₀ (norm_nonneg _) hR, hnorm, sum_sq_le_iff hR]
  rw [mem_latticeDisc_iff_intervals]
  simp only [mem_integerInterval, abs_le, circleHeight]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;>
    constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-- Cardinality is the sum of the exact closed vertical interval counts. -/
theorem card_latticeDisc (c : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    (latticeDisc c R).card = ∑ x ∈ integerInterval (c 0 - R) (c 0 + R),
      (integerInterval (c 1 - circleHeight R (c 0) x)
        (c 1 + circleHeight R (c 0) x)).card := by
  classical
  unfold latticeDisc
  rw [Finset.card_biUnion]
  · simp only [Finset.card_map]
  intro x _ y _ hxy
  apply Finset.disjoint_left.mpr
  intro n hn hm
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hn
  obtain ⟨j, _, hj⟩ := Finset.mem_map.mp hm
  have hx : x = n 0 := congrFun hi 0
  have hy : y = n 0 := congrFun hj 0
  exact hxy (hx.trans hy.symm)

/-- The exact height-plus-sawtooth formula for a translated closed disc.
No boundary points are discarded and neither center coordinate is rounded. -/
theorem card_latticeDisc_eq_height_sub_sawtooth (c : EuclideanSpace ℝ (Fin 2)) (R : ℝ) :
    ((latticeDisc c R).card : ℝ) =
      ∑ x ∈ integerInterval (c 0 - R) (c 0 + R),
        (2 * circleHeight R (c 0) x -
          NumberTheory.sawtooth (c 1 + circleHeight R (c 0) x) -
          NumberTheory.sawtooth (circleHeight R (c 0) x - c 1)) := by
  rw [card_latticeDisc, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hh : 0 ≤ circleHeight R (c 0) x := Real.sqrt_nonneg _
  have hrow : c 1 - circleHeight R (c 0) x ≤ c 1 + circleHeight R (c 0) x := by
    linarith only [hh]
  rw [card_integerInterval_eq_sawtooth hrow, neg_sub]
  ring

end WaveTurbulence.Counting
