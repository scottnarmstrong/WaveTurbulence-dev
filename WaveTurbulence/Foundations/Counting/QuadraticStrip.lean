/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# One-dimensional quadratic strip counting

DH23 `basiccount0pre` (1), elementary branch: the intersection of a line with
an annulus has two components, each of length `O(sqrt (Q*rho))`. The lemmas
here quantify the underlying quadratic argument and integer packing.
-/

public section

namespace WaveTurbulence.Counting

/-- An integer set of real diameter at most `D` has at most `D+1` points. -/
theorem card_int_finset_le_of_diameter (s : Finset ℤ) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ x ∈ s, ∀ y ∈ s, |(x:ℝ)-y| ≤ D) : (s.card:ℝ) ≤ D+1 := by
  classical
  rcases s.eq_empty_or_nonempty with he | hn
  · rw [he,Finset.card_empty,Nat.cast_zero]
    linarith only [hD]
  let lo := s.min' hn
  let hi := s.max' hn
  have hlo : lo ∈ s := s.min'_mem hn
  have hhi : hi ∈ s := s.max'_mem hn
  have hle : lo ≤ hi := s.min'_le_max' hn
  have hsub : s ⊆ Finset.Icc lo hi := fun x hx => Finset.mem_Icc.mpr
    ⟨s.min'_le x hx,s.le_max' x hx⟩
  have hc := Finset.card_le_card hsub
  have hcast := Int.card_Icc_of_le lo hi (by omega : lo ≤ hi+1)
  have hcR : (s.card:ℝ) ≤ (hi:ℝ)-(lo:ℝ)+1 := by
    have hnat : ((s.card:ℤ):ℝ) ≤ (((Finset.Icc lo hi).card:ℤ):ℝ) := by exact_mod_cast hc
    rw [hcast] at hnat
    push_cast at hnat
    linarith only [hnat]
  have hw := hd hi hhi lo hlo
  have hleR : (lo:ℝ) ≤ hi := by exact_mod_cast hle
  rw [abs_of_nonneg (sub_nonneg.mpr hleR)] at hw
  linarith only [hcR,hw]

/-- The quadratic increases by at least the square of the displacement on
one side of its minimum when its leading coefficient is at least one. -/
theorem quadratic_right_displacement_sq_le {A v H K W x y : ℝ}
    (hA : 1 ≤ A) (hv : v ≤ x) (hxy : x ≤ y)
    (hx : |A*(x-v)^2+H-K| ≤ W) (hy : |A*(y-v)^2+H-K| ≤ W) :
    (y-x)^2 ≤ 2*W := by
  have hs : (y-x)^2 ≤ (y-v)^2-(x-v)^2 := by
    have hm := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hv)
    nlinarith only [hm]
  have hs0 : 0 ≤ (y-v)^2-(x-v)^2 := (sq_nonneg _).trans hs
  have hm := mul_nonneg (sub_nonneg.mpr hA) hs0
  have hx' := (abs_le.mp hx).1
  have hy' := (abs_le.mp hy).2
  nlinarith only [hs,hm,hx',hy']

/-- Two points on the right branch of a quadratic strip have distance at most
`sqrt (2*W)`, independently of the level and of the location of the minimum. -/
theorem abs_sub_le_sqrt_of_quadratic_right {A v H K W x y : ℝ}
    (hA : 1 ≤ A) (hW : 0 ≤ W) (hxv : v ≤ x) (hyv : v ≤ y)
    (hx : |A*(x-v)^2+H-K| ≤ W) (hy : |A*(y-v)^2+H-K| ≤ W) :
    |x-y| ≤ Real.sqrt (2*W) := by
  have hs : (x-y)^2 ≤ 2*W := by
    rcases le_total x y with hxy | hyx
    · nlinarith only [quadratic_right_displacement_sq_le hA hxv hxy hx hy]
    · exact quadratic_right_displacement_sq_le hA hyv hyx hy hx
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  simpa only [sq_abs] using hs

/-- Integer points on one side of a quadratic strip admit a square-root count. -/
theorem card_quadratic_strip_right_le (s : Finset ℤ) {A v H K W : ℝ}
    (hA : 1 ≤ A) (hW : 0 ≤ W)
    (hv : ∀ n ∈ s, v ≤ (n:ℝ))
    (hb : ∀ n ∈ s, |A*((n:ℝ)-v)^2+H-K| ≤ W) :
    (s.card:ℝ) ≤ Real.sqrt (2*W)+1 := by
  apply card_int_finset_le_of_diameter s (Real.sqrt_nonneg _)
  intro x hx y hy
  exact abs_sub_le_sqrt_of_quadratic_right hA hW (hv x hx) (hv y hy) (hb x hx) (hb y hy)

/-- The left branch follows by reflecting about zero. -/
theorem abs_sub_le_sqrt_of_quadratic_left {A v H K W x y : ℝ}
    (hA : 1 ≤ A) (hW : 0 ≤ W) (hxv : x ≤ v) (hyv : y ≤ v)
    (hx : |A*(x-v)^2+H-K| ≤ W) (hy : |A*(y-v)^2+H-K| ≤ W) :
    |x-y| ≤ Real.sqrt (2*W) := by
  have he (u : ℝ) : (-u- -v)^2 = (u-v)^2 := by ring
  have hx' : |A*(-x- -v)^2+H-K| ≤ W := by rw [he]; exact hx
  have hy' : |A*(-y- -v)^2+H-K| ≤ W := by rw [he]; exact hy
  have hb := abs_sub_le_sqrt_of_quadratic_right hA hW (neg_le_neg hxv) (neg_le_neg hyv) hx' hy'
  simpa only [neg_sub_neg,abs_sub_comm] using hb

/-- Integer points on the left branch of a quadratic strip. -/
theorem card_quadratic_strip_left_le (s : Finset ℤ) {A v H K W : ℝ}
    (hA : 1 ≤ A) (hW : 0 ≤ W)
    (hv : ∀ n ∈ s, (n:ℝ) ≤ v)
    (hb : ∀ n ∈ s, |A*((n:ℝ)-v)^2+H-K| ≤ W) :
    (s.card:ℝ) ≤ Real.sqrt (2*W)+1 := by
  apply card_int_finset_le_of_diameter s (Real.sqrt_nonneg _)
  intro x hx y hy
  exact abs_sub_le_sqrt_of_quadratic_left hA hW (hv x hx) (hv y hy) (hb x hx) (hb y hy)

/-- A quadratic strip has at most two square-root-sized groups of integer
points, one on either side of its minimum. -/
theorem card_quadratic_strip_le (s : Finset ℤ) {A v H K W : ℝ}
    (hA : 1 ≤ A) (hW : 0 ≤ W)
    (hb : ∀ n ∈ s, |A*((n:ℝ)-v)^2+H-K| ≤ W) :
    (s.card:ℝ) ≤ 2*Real.sqrt (2*W)+2 := by
  classical
  let right := s.filter (fun n : ℤ => v ≤ (n:ℝ))
  let left := s.filter (fun n : ℤ => ¬ v ≤ (n:ℝ))
  have hr := card_quadratic_strip_right_le right hA hW
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => hb n (Finset.mem_filter.mp hn).1)
  have hl := card_quadratic_strip_left_le left hA hW
    (fun n hn => (not_le.mp (Finset.mem_filter.mp hn).2).le)
    (fun n hn => hb n (Finset.mem_filter.mp hn).1)
  have hc : (right.card:ℝ)+(left.card:ℝ) = (s.card:ℝ) := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) (fun n : ℤ => v ≤ (n:ℝ))
  linarith only [hr,hl,hc]

end WaveTurbulence.Counting
