/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.AnnulusRotatedCharts
public import WaveTurbulence.Foundations.Counting.AnnulusCoverGeometry
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Elementary annulus-section lattice counting

DH23 `basiccount0pre` (1), second branch (TeX L2040–L2043). Four Cartesian
charts and a proved short-cell subdivision implement the elementary geometry
argument. A square of radius `L` is allowed in place of the smaller disc.
-/

public section

namespace WaveTurbulence.Counting

/-- The elementary annulus bound uniformly in both centers. The radius is
`r³`; the explicit scale convention is `0 ≤ rho ≤ r³/2` and `r³*rho ≥ 1`.
The containing square is stronger than the source's containing disc. -/
theorem card_annulus_square_le_cube (s : Finset (Fin 2 → ℤ))
    {r rho c₀ c₁ d₀ d₁ L : ℝ} (hr : 0 < r) (hrho : 0 ≤ rho)
    (hrhoQ : rho ≤ r^3/2) (hscale : 1 ≤ r^3*rho) (hL : 0 ≤ L)
    (hproj : ∀ n ∈ s, |(n 0:ℝ)-d₀| ≤ L ∧ |(n 1:ℝ)-d₁| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 640000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  classical
  have hQ := pow_pos hr 3
  have hrhoQ' : rho ≤ r^3 := by linarith only [hrhoQ,hQ]
  let top := s.filter (fun n => r^3/4 ≤ (n 1:ℝ)-c₁)
  let right := s.filter (fun n => r^3/4 ≤ (n 0:ℝ)-c₀)
  let bottom := s.filter (fun n => r^3/4 ≤ c₁-(n 1:ℝ))
  let left := s.filter (fun n => r^3/4 ≤ c₀-(n 0:ℝ))
  let B : ℝ := 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho)
  have hcoords (n : Fin 2 → ℤ) (hn : n ∈ s) := annulus_abs_coordinates_le hrhoQ' (hann n hn)
  have ht : (top.card:ℝ) ≤ B := card_annulus_chart_le_optimized top hr hrho hrhoQ' hscale hL
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (hcoords n (Finset.mem_filter.mp hn).1).1)
    (fun n hn => (hproj n (Finset.mem_filter.mp hn).1).1)
    (fun n hn => hann n (Finset.mem_filter.mp hn).1)
  have hright : (right.card:ℝ) ≤ B := card_annulus_right_chart_le right hr hrho hrhoQ' hscale hL
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (hcoords n (Finset.mem_filter.mp hn).1).2)
    (fun n hn => (hproj n (Finset.mem_filter.mp hn).1).2)
    (fun n hn => hann n (Finset.mem_filter.mp hn).1)
  have hb : (bottom.card:ℝ) ≤ B := card_annulus_lower_chart_le bottom hr hrho hrhoQ' hscale hL
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (hcoords n (Finset.mem_filter.mp hn).1).1)
    (fun n hn => (hproj n (Finset.mem_filter.mp hn).1).1)
    (fun n hn => hann n (Finset.mem_filter.mp hn).1)
  have hleft : (left.card:ℝ) ≤ B := card_annulus_left_chart_le left hr hrho hrhoQ' hscale hL
    (fun n hn => (Finset.mem_filter.mp hn).2)
    (fun n hn => (hcoords n (Finset.mem_filter.mp hn).1).2)
    (fun n hn => (hproj n (Finset.mem_filter.mp hn).1).2)
    (fun n hn => hann n (Finset.mem_filter.mp hn).1)
  have hcover : s ⊆ top ∪ right ∪ bottom ∪ left := by
    intro n hn
    have hc := annulus_mem_four_charts hQ hrhoQ (hann n hn)
    change r^3/4 ≤ (n 1:ℝ)-c₁ ∨ r^3/4 ≤ (n 0:ℝ)-c₀ ∨
      r^3/4 ≤ -((n 1:ℝ)-c₁) ∨ r^3/4 ≤ -((n 0:ℝ)-c₀) at hc
    simp only [top,right,bottom,left,Finset.mem_union,Finset.mem_filter]
    rcases hc with hc | hc | hc | hc
    · exact Or.inl (Or.inl (Or.inl ⟨hn,hc⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hn,hc⟩))
    · exact Or.inl (Or.inr ⟨hn,by linarith only [hc]⟩)
    · exact Or.inr ⟨hn,by linarith only [hc]⟩
  have hc := Finset.card_le_card hcover
  have h₀ := Finset.card_union_le (top ∪ right ∪ bottom) left
  have h₁ := Finset.card_union_le (top ∪ right) bottom
  have h₂ := Finset.card_union_le top right
  have hcard : s.card ≤ top.card+right.card+bottom.card+left.card := by omega
  have hcardR : (s.card:ℝ) ≤ (top.card:ℝ)+(right.card:ℝ)+(bottom.card:ℝ)+(left.card:ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ 4*B := by linarith only [ht,hright,hb,hleft,hcardR]
    _ = _ := by dsimp only [B]; ring

/-- The elementary annulus estimate with the actual radius `Q`. -/
theorem card_annulus_square_le (s : Finset (Fin 2 → ℤ))
    {Q rho c₀ c₁ d₀ d₁ L : ℝ} (hQ : 0 < Q) (hrho : 0 ≤ rho)
    (hrhoQ : rho ≤ Q/2) (hscale : 1 ≤ Q*rho) (hL : 0 ≤ L)
    (hproj : ∀ n ∈ s, |(n 0:ℝ)-d₀| ≤ L ∧ |(n 1:ℝ)-d₁| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-Q| ≤ rho) :
    (s.card:ℝ) ≤ 640000*(1+L*rho+L/Q^((1:ℝ)/3))*Real.sqrt (Q*rho) := by
  let r : ℝ := Q^((1:ℝ)/3)
  have hr : 0 < r := Real.rpow_pos_of_pos hQ _
  have hc : r^3 = Q := by
    simpa only [r,one_div,Nat.cast_ofNat] using
      Real.rpow_inv_natCast_pow hQ.le (show (3:ℕ) ≠ 0 by decide)
  have hb := card_annulus_square_le_cube (r := r) s hr hrho
    (by simpa only [hc] using hrhoQ) (by simpa only [hc] using hscale) hL hproj
    (by simpa only [hc] using hann)
  simpa only [hc,r] using hb

/-- The canonical unit-scale planar lattice norm in Cartesian coordinates. -/
theorem norm_latticePoint_one_sub_eq_sqrt (n : Fin 2 → ℤ)
    (c : EuclideanSpace ℝ (Fin 2)) :
    ‖WaveTurbulence.latticePoint 1 n-c‖ =
      Real.sqrt (((n 0:ℝ)-c 0)^2+((n 1:ℝ)-c 1)^2) := by
  have he : ‖WaveTurbulence.latticePoint 1 n-c‖^2 =
      ((n 0:ℝ)-c 0)^2+((n 1:ℝ)-c 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [WaveTurbulence.latticePoint,Fin.sum_univ_two]
  rw [← he,Real.sqrt_sq (norm_nonneg _)]

/-- DH23 `basiccount0pre` (1), elementary branch, for the actual annulus–disc
intersection. Constants and the width convention `rho ≤ Q/2` are explicit.
The factored bound equals the source's three geometric terms. -/
theorem card_annulus_disc_le (s : Finset (Fin 2 → ℤ))
    (c d : EuclideanSpace ℝ (Fin 2)) {Q rho L : ℝ}
    (hQ : 0 < Q) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ Q/2)
    (hscale : 1 ≤ Q*rho) (hL : 0 ≤ L)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hdisc : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ 640000*(1+L*rho+L/Q^((1:ℝ)/3))*Real.sqrt (Q*rho) := by
  apply card_annulus_square_le s hQ hrho hrhoQ hscale hL
  · intro n hn
    have hp (i : Fin 2) : |(n i:ℝ)-d i| ≤ L := by
      have hc := PiLp.norm_apply_le (p := (2:ENNReal)) (WaveTurbulence.latticePoint 1 n-d) i
      have hc' : |(n i:ℝ)-d i| ≤ ‖WaveTurbulence.latticePoint 1 n-d‖ := by
        simpa [WaveTurbulence.latticePoint] using hc
      exact hc'.trans (hdisc n hn)
    exact ⟨hp 0,hp 1⟩
  · intro n hn
    rw [← norm_latticePoint_one_sub_eq_sqrt]
    exact hann n hn

/-- The factored geometric bound is exactly the sum of the three elementary
terms printed in DH23 `disclattice`. -/
theorem annulus_elementary_terms_eq {Q rho L : ℝ} (hQ : 0 < Q) (hprod : 0 < Q*rho) :
    (1+L*rho+L/Q^((1:ℝ)/3))*Real.sqrt (Q*rho) =
      Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
        L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3)) := by
  have hp : (Q*rho)^((3:ℝ)/2) = (Q*rho)*Real.sqrt (Q*rho) := by
    calc
      _ = (Q*rho)^((1:ℝ)+(1:ℝ)/2) := by congr 1; norm_num
      _ = (Q*rho)^((1:ℝ))*(Q*rho)^((1:ℝ)/2) := Real.rpow_add hprod _ _
      _ = _ := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
  have hm : L*((Q*rho)*Real.sqrt (Q*rho))/Q = L*rho*Real.sqrt (Q*rho) := by
    field_simp
  rw [hp,hm,Real.rpow_neg hQ.le]
  ring

/-- DH23 `basiccount0pre` (1), elementary branch, with the three terms in
exactly the source's expanded form and all inputs proved in Lean. -/
theorem card_annulus_disc_le_expanded (s : Finset (Fin 2 → ℤ))
    (c d : EuclideanSpace ℝ (Fin 2)) {Q rho L : ℝ}
    (hQ : 0 < Q) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ Q/2)
    (hscale : 1 ≤ Q*rho) (hL : 0 ≤ L)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hdisc : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ 640000*(Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
      L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3))) := by
  have he := annulus_elementary_terms_eq (L := L) hQ (lt_of_lt_of_le zero_lt_one hscale)
  calc
    _ ≤ 640000*(1+L*rho+L/Q^((1:ℝ)/3))*Real.sqrt (Q*rho) :=
      card_annulus_disc_le s c d hQ hrho hrhoQ hscale hL hann hdisc
    _ = _ := by rw [← he]; ring

end WaveTurbulence.Counting
