/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.DyadicPowerBlocks
public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Foundations.Counting.CircleArc
import Mathlib.Tactic

/-!
# Dyadic endpoint-distance blocks for outer circular caps

There are at most six integer columns within the terminal endpoint regions.
The other blocks are summed with a convergent geometric weight. The local
block hypothesis is kept explicit pending the shared VdCB phase-class API.
-/

public section

namespace WaveTurbulence.Counting

/-- A unit-scale terminal cutoff exists for every radius at least one. -/
theorem exists_dyadic_unit_cutoff {R : ℝ} (hR : 1 ≤ R) :
    ∃ J : ℕ, 1 ≤ R/(2:ℝ)^J ∧ R/(2:ℝ)^J < 2 := by
  obtain ⟨J,hlo,hhi⟩ := exists_nat_pow_near hR (by norm_num : (1:ℝ) < 2)
  refine ⟨J,?_,?_⟩
  · rw [le_div_iff₀ (by positivity)]
    simpa only [one_mul] using hlo
  · rw [div_lt_iff₀ (by positivity)]
    simpa only [pow_succ,mul_comm] using hhi

/-- At most six actual integer columns lie in endpoint regions of width
strictly less than two, independently of center and radius. -/
theorem card_circle_endpoint_regions_le {R c H : ℝ} (hH : H < 2) :
    (((integerInterval (c-R) (c+R)).filter
      (fun x : ℤ => R-|(x:ℝ)-c| ≤ H)).card:ℝ) ≤ 6 := by
  classical
  let left := integerInterval ((c-R+1)-1) ((c-R+1)+1)
  let right := integerInterval ((c+R-1)-1) ((c+R-1)+1)
  have hs : (integerInterval (c-R) (c+R)).filter (fun x : ℤ => R-|(x:ℝ)-c| ≤ H) ⊆
      left ∪ right := by
    intro x hx
    obtain ⟨hx,hcut⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1,hx2⟩ := (mem_integerInterval _ _ _).mp hx
    by_cases hh : (x:ℝ) ≤ c
    · apply Finset.mem_union_left
      apply (mem_integerInterval _ _ _).mpr
      rw [abs_of_nonpos (sub_nonpos.mpr hh)] at hcut
      constructor <;> linarith only [hx1,hcut,hH]
    · apply Finset.mem_union_right
      apply (mem_integerInterval _ _ _).mpr
      have hx0 : 0 ≤ (x:ℝ)-c := by linarith only [hh]
      rw [abs_of_nonneg hx0] at hcut
      constructor <;> linarith only [hx2,hcut,hH]
  have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le left right)
  have hl := card_integerInterval_le (c-R+1) (by norm_num : (0:ℝ) ≤ 1)
  have hr := card_integerInterval_le (c+R-1) (by norm_num : (0:ℝ) ≤ 1)
  have hc : (((integerInterval (c-R) (c+R)).filter
      (fun x : ℤ => R-|(x:ℝ)-c| ≤ H)).card:ℝ) ≤ (left.card:ℝ)+(right.card:ℝ) := by
    exact_mod_cast hcard
  linarith only [hc,hl,hr]

/-- Actual outer-cap exponential sums follow from their dyadic local
estimates with a bounded geometric factor and an absolute endpoint cost.
No logarithmic loss or unproved exponential-sum theorem is hidden here. -/
theorem norm_outer_cap_sum_le_of_dyadic_bounds (f : ℤ → ℝ)
    {R T c A q : ℝ} (J : ℕ) (hR : 0 ≤ R) (hcut : R/(2:ℝ)^J < 2)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1)
    (hblock : ∀ j < J,
      ‖∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ =>
        T < |(x:ℝ)-c| ∧ R/(2:ℝ)^(j+1) < R-|(x:ℝ)-c| ∧
          R-|(x:ℝ)-c| ≤ R/(2:ℝ)^j), NumberTheory.expPhase (f x)‖ ≤ A*q^(j+1)) :
    ‖∑ x ∈ (integerInterval (c-R) (c+R)).filter (fun x : ℤ => T < |(x:ℝ)-c|),
      NumberTheory.expPhase (f x)‖ ≤ 6+A*(q/(1-q)) := by
  classical
  let s := (integerInterval (c-R) (c+R)).filter (fun x : ℤ => T < |(x:ℝ)-c|)
  let low := s.filter (fun x : ℤ => R-|(x:ℝ)-c| ≤ R/(2:ℝ)^J)
  have hsub : low ⊆ (integerInterval (c-R) (c+R)).filter
      (fun x : ℤ => R-|(x:ℝ)-c| ≤ R/(2:ℝ)^J) := by
    intro x hx
    obtain ⟨hx,hcut⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,hcut⟩
  have hc0 : (low.card:ℝ) ≤ (((integerInterval (c-R) (c+R)).filter
      (fun x : ℤ => R-|(x:ℝ)-c| ≤ R/(2:ℝ)^J)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hc : (low.card:ℝ) ≤ 6 := hc0.trans (card_circle_endpoint_regions_le hcut)
  have hl : ‖∑ x ∈ low, NumberTheory.expPhase (f x)‖ ≤ 6 := by
    calc
      _ ≤ ∑ x ∈ low, ‖NumberTheory.expPhase (f x)‖ := norm_sum_le _ _
      _ = (low.card:ℝ) := by simp only [NumberTheory.norm_expPhase,Finset.sum_const,
        nsmul_eq_mul,mul_one]
      _ ≤ 6 := hc
  apply norm_sum_le_of_dyadic_geometric_bounds s (fun x : ℤ => R-|(x:ℝ)-c|)
    (fun x => NumberTheory.expPhase (f x)) J hR
    (fun x hx => sub_le_self R (abs_nonneg _)) hA hq hq1 hl
  intro j hj
  simpa only [s,Finset.filter_filter,and_assoc] using hblock j hj

end WaveTurbulence.Counting
