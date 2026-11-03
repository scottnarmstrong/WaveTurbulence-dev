/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic

/-!
# Signed short-relation indices and their harmonic weights

DH23 `estcross`: separate a nonzero integer coefficient into its sign and
positive magnitude, then sum its reciprocal explicitly. The other coefficient
ranges over the actual closed integer interval `[-M,M]`.
-/

public section

namespace WaveTurbulence.Counting

/-- A natural magnitude with one of its two integer signs. -/
@[expose] def signedNat (sign : Bool) (n : ℕ) : ℤ := if sign then (n:ℤ) else -(n:ℤ)

/-- The magnitude of a signed natural, viewed as a real number. -/
theorem abs_signedNat (sign : Bool) (n : ℕ) : |(signedNat sign n:ℝ)| = (n:ℝ) := by
  cases sign <;> simp only [signedNat,Bool.false_eq_true,ite_false,ite_true,
    Int.cast_neg,Int.cast_natCast,abs_neg,abs_of_nonneg (show (0:ℝ) ≤ (n:ℝ) from Nat.cast_nonneg n)]

/-- Every integer has a signed-natural representation with its actual magnitude. -/
theorem exists_signedNat_eq (m : ℤ) : ∃ sign : Bool, signedNat sign m.natAbs = m := by
  by_cases hm : 0 ≤ m
  · exact ⟨true,by simpa only [signedNat,ite_true] using Int.natAbs_of_nonneg hm⟩
  · exact ⟨false,by
      simp only [signedNat,Bool.false_eq_true,ite_false]
      exact (Int.eq_neg_natAbs_of_nonpos (not_le.mp hm).le).symm⟩

/-- Actual finite indices for a relation with one arbitrary coefficient and
one nonzero coefficient, both of magnitude at most `M`. -/
@[expose] def relationIndices (M : ℕ) : Finset (Bool × (ℤ × ℕ)) :=
  Finset.univ.product ((Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M))

/-- The unrestricted first coefficient of a relation index. -/
@[expose] def relationFirst (w : Bool × (ℤ × ℕ)) : ℤ := w.2.1

/-- The signed nonzero second coefficient of a relation index. -/
@[expose] def relationSecond (w : Bool × (ℤ × ℕ)) : ℤ := signedNat w.1 w.2.2

/-- Bounds and nonvanishing of the coefficients encoded by an actual index. -/
theorem relationIndices_bounds {M : ℕ} {w : Bool × (ℤ × ℕ)}
    (hw : w ∈ relationIndices M) :
    |relationFirst w| ≤ (M:ℤ) ∧ relationSecond w ≠ 0 ∧ |(relationSecond w:ℝ)| ≤ (M:ℝ) := by
  have hh := Finset.mem_product.mp hw
  have hb := Finset.mem_product.mp hh.2
  have hm := Finset.mem_Icc.mp hb.1
  have hn := Finset.mem_Icc.mp hb.2
  have hfirst : |relationFirst w| ≤ (M:ℤ) := abs_le.mpr hm
  have hsecond : |(relationSecond w:ℝ)| = (w.2.2:ℝ) := abs_signedNat _ _
  refine ⟨hfirst,?_,?_⟩
  · intro he
    rw [he,Int.cast_zero,abs_zero] at hsecond
    have hpos : (1:ℝ) ≤ w.2.2 := by exact_mod_cast hn.1
    linarith only [hsecond,hpos]
  · rw [hsecond]
    exact_mod_cast hn.2

/-- Every pair with bounded integer coefficients and a nonzero second
coefficient occurs in the finite index set. -/
theorem exists_mem_relationIndices {M : ℕ} (m n : ℤ) (hn : n ≠ 0)
    (hmabs : |m| ≤ (M:ℤ)) (hnabs : |n| ≤ (M:ℤ)) :
    ∃ w ∈ relationIndices M, relationFirst w = m ∧ relationSecond w = n := by
  obtain ⟨sign,hsign⟩ := exists_signedNat_eq n
  have hn1 : 1 ≤ n.natAbs := by
    have hh : n.natAbs ≠ 0 := by
      intro he
      exact hn (Int.natAbs_eq_zero.mp he)
    omega
  have hnM : n.natAbs ≤ M := by
    have hh : (n.natAbs:ℤ) ≤ (M:ℤ) := by rw [Int.natCast_natAbs]; exact hnabs
    exact_mod_cast hh
  refine ⟨(sign,(m,n.natAbs)),?_,rfl,hsign⟩
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_univ _,Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr (abs_le.mp hmabs),Finset.mem_Icc.mpr ⟨hn1,hnM⟩⟩⟩

/-- Real coefficient bounds suffice for membership in the integer index set. -/
theorem exists_mem_relationIndices_of_real_bounds {M : ℕ} (m n : ℤ) (hn : n ≠ 0)
    (hmabs : |(m:ℝ)| ≤ (M:ℝ)) (hnabs : |(n:ℝ)| ≤ (M:ℝ)) :
    ∃ w ∈ relationIndices M, relationFirst w = m ∧ relationSecond w = n := by
  rw [← Int.cast_abs] at hmabs hnabs
  apply exists_mem_relationIndices m n hn
  · exact_mod_cast hmabs
  · exact_mod_cast hnabs

/-- Exact reciprocal-weight sum over the short-relation index set. -/
theorem sum_relationIndices_inv_abs (M : ℕ) :
    (∑ w ∈ relationIndices M, 1/|(relationSecond w:ℝ)|) =
      2*(2*(M:ℝ)+1)*(harmonic M:ℝ) := by
  have hsum : (∑ j ∈ Finset.Icc 1 M, 1/(j:ℝ)) = (harmonic M:ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  have hcardZ := Int.card_Icc_of_le (-(M:ℤ)) M (by omega : -(M:ℤ) ≤ M+1)
  have hcard : ((Finset.Icc (-(M:ℤ)) M).card:ℝ) = 2*(M:ℝ)+1 := by
    have hc := congrArg (fun z : ℤ => (z:ℝ)) hcardZ
    push_cast at hc
    linarith only [hc]
  change (∑ w ∈ Finset.univ.product ((Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M)),
    1/|(signedNat w.1 w.2.2:ℝ)|) = _
  have houter :
      (∑ w ∈ Finset.univ.product ((Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M)),
        1/|(signedNat w.1 w.2.2:ℝ)|) =
      ∑ sign : Bool, ∑ w ∈ (Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M),
        1/|(signedNat sign w.2:ℝ)| := by
    simpa only using! Finset.sum_product (Finset.univ : Finset Bool)
      ((Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M))
      (fun w : Bool × (ℤ × ℕ) => 1/|(signedNat w.1 w.2.2:ℝ)|)
  have hinner (sign : Bool) :
      (∑ w ∈ (Finset.Icc (-(M:ℤ)) M).product (Finset.Icc 1 M),
        1/|(signedNat sign w.2:ℝ)|) =
      ∑ _m ∈ Finset.Icc (-(M:ℤ)) M, ∑ j ∈ Finset.Icc 1 M,
        1/|(signedNat sign j:ℝ)| := by
    simpa only using! Finset.sum_product (Finset.Icc (-(M:ℤ)) M) (Finset.Icc 1 M)
      (fun w : ℤ × ℕ => 1/|(signedNat sign w.2:ℝ)|)
  rw [houter]
  simp_rw [hinner,abs_signedNat,hsum]
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_bool,Nat.cast_ofNat]
  rw [hcard]
  ring

/-- The relation-weight sum has a single logarithmic loss. -/
theorem sum_relationIndices_inv_abs_le (M : ℕ) (hM : 1 ≤ M) :
    (∑ w ∈ relationIndices M, 1/|(relationSecond w:ℝ)|) ≤
      6*(M:ℝ)*(1+Real.log M) := by
  rw [sum_relationIndices_inv_abs]
  have hlog : 0 ≤ 1+Real.log (M:ℝ) := by
    have hMr : (1:ℝ) ≤ M := by exact_mod_cast hM
    have hh := Real.log_nonneg hMr
    linarith only [hh]
  have hcoef : 2*(2*(M:ℝ)+1) ≤ 6*(M:ℝ) := by
    have hh : (1:ℝ) ≤ M := by exact_mod_cast hM
    linarith only [hh]
  calc
    _ ≤ (2*(2*(M:ℝ)+1))*(1+Real.log M) :=
      mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hlog

end WaveTurbulence.Counting
