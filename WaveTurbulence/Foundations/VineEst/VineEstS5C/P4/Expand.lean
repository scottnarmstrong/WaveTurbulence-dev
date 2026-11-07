/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Complex.Basic
public import WaveTurbulence.Foundations.VineEst.VineEstS4c.ReplaceAlgebra
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.BundleAbs

/-! # P4: the pieces (a)-(c) and the remainder rows as sums of products of separated terms (V5 Step 4d part C)

Generic algebra (no vine data).  `Q b = ∑ i, sQ b i`, `T b = ∑ j, sT b j` at the two time points of the bundle give the summands
`tA1, tA2, tKQ, tTQ, tKT, tTT` (indexed by `(b, i, j)`) of the pieces of `replSum_decomp_ext`, and `rA1, rA2, rA3, rB1, rB2, rB3` of the remainder rows
`remA`, `remB` (indexed by `(b, i)`, `(b, j)`, `b`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.P4
open WaveTurbulence WaveTurbulence.VineEstS4c Finset
open scoped ComplexConjugate

variable {β : Type*} {d : ℕ}

/-- The point-level data: separated terms of the couple and tree families. -/
structure SepTerms (β : Type*) (d : ℕ) where
  mQ : β → ℕ
  mT : β → ℕ
  sQ : ∀ b, Fin (mQ b) → ℝ → ℝ → Mom d → ℂ
  sT : ∀ b, Fin (mT b) → ℝ → ℝ → Mom d → ℂ

variable (S : SepTerms β d) (t0 s1 t1 : ℝ) (x y : Mom d)

open Classical in
/-- Clause (a), II-a: `s₁ ≤ t₀ < t₁`. -/
noncomputable def tA1 (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if s1 ≤ t0 ∧ t0 < t1 then conj (S.sQ b i s1 t0 y) * S.sT b j t1 t0 x else 0
open Classical in
/-- Clause (a), II-b: `t₁ ≤ t₀ < s₁`. -/
noncomputable def tA2 (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if t1 ≤ t0 ∧ t0 < s1 then S.sQ b i t1 t0 x * conj (S.sT b j s1 t0 y) else 0
open Classical in
noncomputable def tKQ (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if t0 < t1 ∧ t0 < s1 then conj (S.sQ b i s1 t0 y - S.sQ b i s1 t0 x) * S.sT b j t1 t0 x else 0
open Classical in
noncomputable def tTQ (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if t0 < t1 ∧ t0 < s1 then conj (S.sQ b i s1 t0 x - S.sQ b i t1 t0 x) * S.sT b j t1 t0 x else 0
open Classical in
noncomputable def tKT (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if t0 < t1 ∧ t0 < s1 then S.sQ b i t1 t0 x * conj (S.sT b j s1 t0 x - S.sT b j s1 t0 y) else 0
open Classical in
noncomputable def tTT (b : β) (i : Fin (S.mQ b)) (j : Fin (S.mT b)) : ℂ :=
  if t0 < t1 ∧ t0 < s1 then S.sQ b i t1 t0 x * conj (S.sT b j t1 t0 x - S.sT b j s1 t0 x) else 0

section Expand
variable (Q T RQ RT : β → ℝ → ℝ → Mom d → ℂ) (bs : Finset β)
  (hQ : ∀ b ∈ bs, (∀ k, Q b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, Q b t1 t0 k = ∑ i, S.sQ b i t1 t0 k)
  (hT : ∀ b ∈ bs, (∀ k, T b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, T b t1 t0 k = ∑ j, S.sT b j t1 t0 k)

include hQ hT

theorem pieceA1_expand : pieceA1 bs T (cswap Q) t0 s1 t1 x y = ∑ b ∈ bs, ∑ i, ∑ j, tA1 S t0 s1 t1 x y b i j := by
  classical
  unfold pieceA1
  split_ifs with h
  · refine Finset.sum_congr rfl fun b hb => ?_
    simp only [cswap, tA1, if_pos h, (hQ b hb).1, (hT b hb).2, map_sum, Finset.sum_mul_sum]
  · simp [tA1, h]

theorem pieceA2_expand : pieceA2 bs Q (cconj T) t0 s1 t1 x y = ∑ b ∈ bs, ∑ i, ∑ j, tA2 S t0 s1 t1 x y b i j := by
  classical
  unfold pieceA2
  split_ifs with h
  · refine Finset.sum_congr rfl fun b hb => ?_
    simp only [cconj, tA2, if_pos h, (hQ b hb).2, (hT b hb).1, map_sum, Finset.sum_mul_sum]
  · simp [tA2, h]

theorem pieceKQ_expand (h : t0 < t1 ∧ t0 < s1) :
    pieceKQ bs Q T t0 s1 t1 x y = ∑ b ∈ bs, ∑ i, ∑ j, tKQ S t0 s1 t1 x y b i j := by
  classical
  unfold pieceKQ
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [tKQ, if_pos h, (hQ b hb).1, (hT b hb).2, ← Finset.sum_sub_distrib, map_sum, Finset.sum_mul_sum]

theorem pieceTQ_expand (h : t0 < t1 ∧ t0 < s1) :
    pieceTQ bs Q T t0 s1 t1 x = ∑ b ∈ bs, ∑ i, ∑ j, tTQ S t0 s1 t1 x b i j := by
  classical
  unfold pieceTQ
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [tTQ, if_pos h, (hQ b hb).1, (hQ b hb).2, (hT b hb).2, ← Finset.sum_sub_distrib, map_sum, Finset.sum_mul_sum]

theorem pieceKT_expand (h : t0 < t1 ∧ t0 < s1) :
    pieceKT bs Q T t0 s1 t1 x y = ∑ b ∈ bs, ∑ i, ∑ j, tKT S t0 s1 t1 x y b i j := by
  classical
  unfold pieceKT
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [tKT, if_pos h, (hQ b hb).2, (hT b hb).1, ← Finset.sum_sub_distrib, map_sum, Finset.sum_mul_sum]

theorem pieceTT_expand (h : t0 < t1 ∧ t0 < s1) :
    pieceTT bs Q T t0 s1 t1 x = ∑ b ∈ bs, ∑ i, ∑ j, tTT S t0 s1 t1 x b i j := by
  classical
  unfold pieceTT
  refine Finset.sum_congr rfl fun b hb => ?_
  simp only [tTT, if_pos h, (hQ b hb).2, (hT b hb).1, (hT b hb).2, ← Finset.sum_sub_distrib, map_sum, Finset.sum_mul_sum]

end Expand

section Rem
variable (RQ RT : β → ℝ → ℝ → Mom d → ℂ)

open Classical in
noncomputable def rA1 (b : β) (i : Fin (S.mQ b)) : ℂ :=
  if t0 < t1 then conj (S.sQ b i s1 t0 y) * RT b t1 t0 x else 0
open Classical in
noncomputable def rA2 (b : β) (j : Fin (S.mT b)) : ℂ :=
  if t0 < t1 then conj (RQ b s1 t0 y) * S.sT b j t1 t0 x else 0
open Classical in
noncomputable def rA3 (b : β) : ℂ :=
  if t0 < t1 then conj (RQ b s1 t0 y) * RT b t1 t0 x else 0
open Classical in
noncomputable def rB1 (b : β) (i : Fin (S.mQ b)) : ℂ :=
  if t0 < s1 then S.sQ b i t1 t0 x * conj (RT b s1 t0 y) else 0
open Classical in
noncomputable def rB2 (b : β) (j : Fin (S.mT b)) : ℂ :=
  if t0 < s1 then RQ b t1 t0 x * conj (S.sT b j s1 t0 y) else 0
open Classical in
noncomputable def rB3 (b : β) : ℂ :=
  if t0 < s1 then RQ b t1 t0 x * conj (RT b s1 t0 y) else 0

variable (Q T : β → ℝ → ℝ → Mom d → ℂ) (b : β)
  (hQ : (∀ k, Q b s1 t0 k = ∑ i, S.sQ b i s1 t0 k) ∧ ∀ k, Q b t1 t0 k = ∑ i, S.sQ b i t1 t0 k)
  (hT : (∀ k, T b s1 t0 k = ∑ j, S.sT b j s1 t0 k) ∧ ∀ k, T b t1 t0 k = ∑ j, S.sT b j t1 t0 k)

include hQ hT

theorem remA_expand :
    remA Q T RQ RT b t0 s1 t1 x y =
      (∑ i, rA1 S t0 s1 t1 x y RT b i) + (∑ j, rA2 S t0 s1 t1 x y RQ b j) + rA3 t0 s1 t1 x y RQ RT b := by
  classical
  unfold remA rA1 rA2 rA3
  by_cases h : t0 < t1
  · simp only [if_pos h, one_mul, cswap, hQ.1, hT.2, map_sum, Finset.sum_mul, ← Finset.mul_sum, mul_add]
    rw [Finset.mul_sum]; ring
  · simp [h]

theorem remB_expand :
    remB Q T RQ RT b t0 s1 t1 x y =
      (∑ i, rB1 S t0 s1 t1 x y RT b i) + (∑ j, rB2 S t0 s1 t1 x y RQ b j) + rB3 t0 s1 t1 x y RQ RT b := by
  classical
  unfold remB rB1 rB2 rB3
  by_cases h : t0 < s1
  · simp only [if_pos h, one_mul, cconj, hQ.2, hT.1, map_sum, Finset.sum_mul, ← Finset.mul_sum, mul_add]
    rw [Finset.mul_sum]; ring
  · simp [h]

end Rem

end WaveTurbulence.VineEstS5C.P4
