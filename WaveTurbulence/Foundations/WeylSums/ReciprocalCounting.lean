/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas

/-!
# Reciprocal counting on arithmetic progressions

Harmonic bounds used when summing capped inverse distances in the Gauss lemma.
The standalone sharp interval estimate uses `log(2K)` to include `K = 1`;
this is equivalent up to an absolute constant to `log K` for `K ≥ 2`.
-/

public section

open scoped BigOperators
open Finset

namespace WaveTurbulence.WeylSums

/-- The zero reciprocal contributes nothing, leaving the usual harmonic sum. -/
theorem sum_inv_range_succ (M : ℕ) :
    (∑ j ∈ range (M + 1), (j : ℝ)⁻¹) = (harmonic M : ℝ) := by
  rw [sum_range_succ']
  simp only [Nat.cast_zero, inv_zero, add_zero, harmonic, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]

/-- The reciprocal distances from any index have harmonic total mass. -/
theorem sum_inv_distance_le (M a : ℕ) (ha : a < M) :
    (∑ j ∈ range M, |(j : ℝ) - a|⁻¹) ≤ 2 * (harmonic M : ℝ) := by
  have hleft : (∑ j ∈ range M with j < a, |(j : ℝ) - a|⁻¹) ≤ (harmonic M : ℝ) := by
    rw [← sum_inv_range_succ]
    refine sum_le_sum_of_injOn (fun j => a - j) ?_ ?_ ?_ ?_
    · intro i hi j hj hij
      simp only [mem_coe, mem_filter, mem_range] at hi hj
      dsimp at hij
      omega
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      simp only [mem_filter, mem_range] at hj ⊢
      omega
    · intro j hj
      simp only [mem_filter, mem_range] at hj
      have hja : (j : ℝ) ≤ a := Nat.cast_le.mpr hj.2.le
      rw [abs_of_nonpos (sub_nonpos.mpr hja), neg_sub, Nat.cast_sub hj.2.le]
    · intro j _ _
      positivity
  have hright : (∑ j ∈ range M with ¬j < a, |(j : ℝ) - a|⁻¹) ≤
      (harmonic M : ℝ) := by
    rw [← sum_inv_range_succ]
    refine sum_le_sum_of_injOn (fun j => j - a) ?_ ?_ ?_ ?_
    · intro i hi j hj hij
      simp only [mem_coe, mem_filter, mem_range] at hi hj
      dsimp at hij
      omega
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
      simp only [mem_filter, mem_range] at hj ⊢
      omega
    · intro j hj
      simp only [mem_filter, mem_range, not_lt] at hj
      have haj : (a : ℝ) ≤ j := Nat.cast_le.mpr hj.2
      rw [abs_of_nonneg (sub_nonneg.mpr haj), Nat.cast_sub hj.2]
    · intro j _ _
      positivity
  have hsplit := sum_filter_add_sum_filter_not (range M) (fun j => j < a)
    (fun j => |(j : ℝ) - a|⁻¹)
  linarith only [hleft, hright, hsplit]

/-- Integer reciprocal distances on a symmetric interval have harmonic mass. -/
theorem sum_inv_int_Icc_le (R : ℕ) :
    (∑ n ∈ Icc (-(R : ℤ)) R, |(n : ℝ)|⁻¹) ≤ 2 * (harmonic R : ℝ) := by
  have hhalf (negative : Bool) :
      (∑ n ∈ (Icc (-(R : ℤ)) R).filter
        (fun n => if negative then n < 0 else 0 ≤ n), |(n : ℝ)|⁻¹) ≤
      (harmonic R : ℝ) := by
    rw [← sum_inv_range_succ]
    refine sum_le_sum_of_injOn Int.natAbs ?_ ?_ ?_ ?_
    · intro i hi j hj heq
      simp only [mem_coe, mem_filter, mem_Icc] at hi hj
      cases negative with
      | false =>
        exact (Int.natAbs_inj_of_nonneg_of_nonneg hi.2 hj.2).mp heq
      | true =>
        exact (Int.natAbs_inj_of_nonpos_of_nonpos hi.2.le hj.2.le).mp heq
    · intro k hk
      obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
      simp only [mem_filter, mem_Icc] at hn
      rw [mem_range, Nat.lt_succ_iff]
      rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
      exact abs_le.mpr hn.1
    · intro n _
      rw [Nat.cast_natAbs, Int.cast_abs]
    · intro n _ _
      positivity
  have hsplit := sum_filter_add_sum_filter_not (Icc (-(R : ℤ)) R) (fun n => n < 0)
    (fun n => |(n : ℝ)|⁻¹)
  have hl := hhalf true
  have hr := hhalf false
  simp only [ite_false, ite_true, Bool.false_eq_true] at hl hr
  simp only [not_lt] at hsplit
  linarith only [hl, hr, hsplit]


/-- Sum an explicit envelope: seventeen near-integer terms and harmonic tails. -/
theorem sum_int_envelope_le (R : ℕ) (A C : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    (∑ n ∈ Icc (-(R : ℤ)) R, if |n| ≤ 8 then A else C / |(n : ℝ)|) ≤
      17 * A + 2 * C * (harmonic R : ℝ) := by
  classical
  let S := Icc (-(R : ℤ)) R
  have hsplit := sum_filter_add_sum_filter_not S (fun n : ℤ => |n| ≤ 8)
    (fun n => if |n| ≤ 8 then A else C / |(n : ℝ)|)
  have hcard : (((S.filter (fun n : ℤ => |n| ≤ 8)).card) : ℝ) ≤ 17 := by
    have hsub : S.filter (fun n : ℤ => |n| ≤ 8) ⊆ Icc (-8 : ℤ) 8 := by
      intro n hn
      exact mem_Icc.mpr (abs_le.mp (mem_filter.mp hn).2)
    have hc := card_le_card hsub
    norm_num at hc
    exact_mod_cast hc
  have hnear : (∑ n ∈ S.filter (fun n : ℤ => |n| ≤ 8),
      if |n| ≤ 8 then A else C / |(n : ℝ)|) ≤ 17 * A := by
    calc
      _ = ((S.filter (fun n : ℤ => |n| ≤ 8)).card : ℝ) * A := by
        rw [← nsmul_eq_mul, ← sum_const]
        apply sum_congr rfl
        intro n hn
        rw [ite_eq_left (mem_filter.mp hn).2]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hA
  have hfar : (∑ n ∈ S.filter (fun n : ℤ => ¬|n| ≤ 8),
      if |n| ≤ 8 then A else C / |(n : ℝ)|) ≤ 2 * C * (harmonic R : ℝ) := by
    calc
      _ = ∑ n ∈ S.filter (fun n : ℤ => ¬|n| ≤ 8), C / |(n : ℝ)| := by
        apply sum_congr rfl
        intro n hn
        rw [ite_eq_right (mem_filter.mp hn).2]
      _ ≤ ∑ n ∈ S, C / |(n : ℝ)| :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => div_nonneg hC (abs_nonneg _))
      _ = C * ∑ n ∈ S, |(n : ℝ)|⁻¹ := by simp only [div_eq_mul_inv, mul_sum]
      _ ≤ C * (2 * (harmonic R : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_int_Icc_le R) hC
      _ = _ := by ring
  linarith only [hnear, hfar, hsplit]


/-- A capped reciprocal, taking the value `T` at zero as required for resonances. -/
@[expose] noncomputable def cappedInv (T x : ℝ) : ℝ :=
  if x = 0 then T else min T |x|⁻¹

@[simp] theorem cappedInv_abs (T x : ℝ) : cappedInv T |x| = cappedInv T x := by
  simp only [cappedInv, abs_eq_zero, abs_abs]


theorem cappedInv_le (T x : ℝ) : cappedInv T x ≤ T := by
  unfold cappedInv
  split
  · exact le_rfl
  · exact min_le_left _ _

theorem cappedInv_nonneg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : 0 ≤ cappedInv T x := by
  unfold cappedInv
  split
  · exact hT
  · exact le_min hT (inv_nonneg.mpr (abs_nonneg _))

theorem cappedInv_le_inv (T : ℝ) {x : ℝ} (hx : x ≠ 0) :
    cappedInv T x ≤ |x|⁻¹ := by
  rw [cappedInv, ite_eq_right hx]
  exact min_le_right _ _

/-- On an affine progression with nonzero step, only one term needs the cap;
the other terms are bounded by a harmonic sum. -/
theorem sum_cappedInv_affine_le (T x δ : ℝ) (M : ℕ) (hT : 0 ≤ T) (hδ : δ ≠ 0) :
    (∑ j ∈ range M, cappedInv T (x + δ * j)) ≤
      T + 4 / |δ| * (harmonic M : ℝ) := by
  classical
  by_cases hM : M = 0
  · subst M
    simpa only [range_zero, sum_empty, harmonic_zero, Rat.cast_zero, mul_zero, add_zero]
      using hT
  obtain ⟨a, ha, hmin⟩ := (range M).exists_min_image (fun j => |x + δ * j|)
    (nonempty_range_iff.mpr hM)
  have hδpos : 0 < |δ| := abs_pos.mpr hδ
  have hterm : ∀ j ∈ (range M).erase a,
      cappedInv T (x + δ * j) ≤ 2 / |δ| * |(j : ℝ) - a|⁻¹ := by
    intro j hj
    obtain ⟨hja, hjM⟩ := mem_erase.mp hj
    have hja' : (j : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hja)
    have hdist : 0 < |(j : ℝ) - a| := abs_pos.mpr hja'
    have hsep : |δ| * |(j : ℝ) - a| ≤ 2 * |x + δ * j| := by
      calc
        _ = |(x + δ * j) - (x + δ * a)| := by rw [← abs_mul]; congr 1; ring
        _ ≤ |x + δ * j| + |x + δ * a| := abs_sub _ _
        _ ≤ 2 * |x + δ * j| := by linarith only [hmin j hjM]
    have hxpos : 0 < |x + δ * j| := by
      have hp := mul_pos hδpos hdist
      linarith only [hp, hsep]
    refine (cappedInv_le_inv T (abs_pos.mp hxpos)).trans ?_
    have hi : |x + δ * j|⁻¹ ≤ 2 / (|δ| * |(j : ℝ) - a|) := by
      rw [inv_eq_one_div]
      exact (div_le_div_iff₀ hxpos (mul_pos hδpos hdist)).mpr (by simpa using hsep)
    calc
      _ ≤ 2 / (|δ| * |(j : ℝ) - a|) := hi
      _ = 2 / |δ| * |(j : ℝ) - a|⁻¹ := by rw [div_mul_eq_div_div, div_eq_mul_inv]
  have hsum : (∑ j ∈ (range M).erase a, cappedInv T (x + δ * j)) ≤
      2 / |δ| * (2 * (harmonic M : ℝ)) := by
    calc
      _ ≤ ∑ j ∈ (range M).erase a, 2 / |δ| * |(j : ℝ) - a|⁻¹ := sum_le_sum hterm
      _ ≤ ∑ j ∈ range M, 2 / |δ| * |(j : ℝ) - a|⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun j _ _ => by positivity)
      _ = 2 / |δ| * ∑ j ∈ range M, |(j : ℝ) - a|⁻¹ := (mul_sum ..).symm
      _ ≤ 2 / |δ| * (2 * (harmonic M : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_inv_distance_le M a (mem_range.mp ha)) (by positivity)
  rw [← sum_erase_add _ _ ha]
  have hc := cappedInv_le T (x + δ * a)
  calc
    _ ≤ 2 / |δ| * (2 * (harmonic M : ℝ)) + T := add_le_add hsum hc
    _ = T + 4 / |δ| * (harmonic M : ℝ) := by ring


end WaveTurbulence.WeylSums
