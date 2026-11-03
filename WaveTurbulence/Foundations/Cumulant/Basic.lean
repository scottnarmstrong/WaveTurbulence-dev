/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.Complex.Basic
import Mathlib.Probability.Notation
import Mathlib.Data.Finset.Grade
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Cumulants against an arbitrary measure

TARGET Definition `defcm`, equation `eqncm` (L570–L573). The measure is not
normalized: expectations under an event use the restriction of the original measure.
The empty-set value of this literal formula is one.
-/

public section

open MeasureTheory ProbabilityTheory

namespace WaveTurbulence

/-- The cumulant `𝕂((X_j)_{j ∈ s})` of TARGET Def `defcm` (eqncm), with expectations taken against a measure `μ`
(`μ = P.restrict F` for "assuming the event `F`"): the sum over all partitions `𝒫` of `s` of
`(-1)^{|𝒫|-1} (|𝒫|-1)! ∏_{A ∈ 𝒫} 𝔼 ∏_{j ∈ A} X_j`. -/
@[expose] noncomputable def cumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω) (X : ι → Ω → ℂ)
    (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
    ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ

/-- The literal partition formula has empty-set value one. Gaussian vanishing is
therefore stated only for nonempty sets, as authorized in the CUMUL packet ruling. -/
theorem cumulant_empty {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) : cumulant μ X ∅ = 1 := by
  classical
  unfold cumulant
  have hp (P : Finpartition (∅ : Finset ι)) : P.parts = ∅ :=
    P.parts_eq_empty_iff.mpr rfl
  simp only [hp, Finset.card_empty, zero_tsub, pow_zero, Nat.factorial_zero,
    Nat.cast_one, mul_one, Finset.prod_empty]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_eq_one]
  exact Fintype.card_ofSubsingleton (Finpartition.empty (Finset ι))

/-- Products over all blocks of a partition count each index exactly once. -/
theorem prod_finpartition_parts {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    {s : Finset ι} (P : Finpartition s) (c : ι → M) :
    (∏ A ∈ P.parts, ∏ j ∈ A, c j) = ∏ j ∈ s, c j := by
  have h := Finset.prod_biUnion (s := P.parts) (t := id) (f := c)
    (fun A hA B hB hAB => P.disjoint hA hB hAB)
  rw [P.biUnion_parts] at h
  exact h.symm

/-- Scalar multiplication in every entry factors out of the cumulant, without
normalizing the underlying measure (TARGET Definition `defcm`). -/
theorem cumulant_mul {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (c : ι → ℂ) (s : Finset ι) :
    cumulant μ (fun j ω => c j * X j ω) s = (∏ j ∈ s, c j) * cumulant μ X s := by
  classical
  unfold cumulant
  simp_rw [Finset.prod_mul_distrib, integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P _
  rw [Finset.prod_mul_distrib, prod_finpartition_parts]
  ring

/-- First-order cumulants are moments, including for unnormalized measures. -/
theorem cumulant_singleton {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (i : ι) :
    cumulant μ X {i} = ∫ ω, X i ω ∂μ := by
  classical
  let _ := (Finset.isAtom_singleton i).uniqueFinpartition
    (P := Finpartition.indiscrete (by simp : ({i} : Finset ι) ≠ ⊥))
  unfold cumulant
  rw [Fintype.sum_unique]
  change (-1 : ℂ) ^ (1 - 1) * ((1 - 1).factorial : ℂ) *
    (∏ A ∈ ({({i} : Finset ι)} : Finset (Finset ι)), ∫ ω, ∏ j ∈ A, X j ω ∂μ) = _
  simp

end WaveTurbulence
