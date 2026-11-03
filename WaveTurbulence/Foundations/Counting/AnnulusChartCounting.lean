/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.AnnulusSectionGeometry
public import WaveTurbulence.Foundations.Counting.AnnulusLine
public import WaveTurbulence.Foundations.Counting.IntervalCells
public import WaveTurbulence.Foundations.Counting.AnnulusCellWidth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Counting an annulus in one Cartesian chart

DH23 `basiccount0pre` (1), elementary branch: partition into short horizontal
cells, prove collinearity in each cell, and sum the uniform annulus-line bound.
The cell width is an explicit geometric parameter, chosen in the final estimate.
-/

public section

namespace WaveTurbulence.Counting

/-- The short-cell annulus estimate in the upper Cartesian chart. -/
theorem card_annulus_chart_le (s : Finset (Fin 2 → ℤ))
    {Q rho T c₀ c₁ d L : ℝ}
    (hQ : 0 < Q) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ Q) (hscale : 1 ≤ Q*rho)
    (hT : 0 < T) (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, Q/4 ≤ (n 1:ℝ)-c₁)
    (hhorizontal : ∀ n ∈ s, |(n 0:ℝ)-c₀| ≤ 2*Q)
    (hproj : ∀ n ∈ s, |(n 0:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-Q| ≤ rho)
    (hthin : 2*T*(1000*(rho+T^2/Q)) < 1) :
    (s.card:ℝ) ≤ (2*L/T+2)*(8*Real.sqrt (Q*rho)) := by
  classical
  let f : (Fin 2 → ℤ) → ℤ := fun n => ⌊(n 0:ℝ)/T⌋
  have hband (n : Fin 2 → ℤ) (hn : n ∈ s) :
      |((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2-Q^2| ≤ 3*Q*rho := by
    have hb := abs_sq_sub_sq_le_of_abs_sub_le (Real.sqrt_nonneg _) hQ.le hrho (hann n hn)
    rw [Real.sq_sqrt (by positivity)] at hb
    have hm := mul_nonneg hrho (sub_nonneg.mpr hrhoQ)
    nlinarith only [hb,hm]
  have hfiber (k : ℤ) : ((s.filter (fun n => f n = k)).card:ℝ) ≤ 8*Real.sqrt (Q*rho) := by
    let t := s.filter (fun n => f n = k)
    have hsub : t ⊆ s := Finset.filter_subset _ _
    have hdet := lattice_annulus_chart_triangles_eq_zero t hQ hrho hrhoQ hT.le
      (fun n hn => hchart n (hsub hn)) (fun n hn => hhorizontal n (hsub hn))
      (by
        intro p hp q hq
        apply abs_sub_le_of_floor_div_eq hT
        exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hp).2.symm)
      (fun n hn => hband n (hsub hn)) hthin
    exact card_collinear_radial_annulus_le t hQ.le hrho hrhoQ hscale hdet
      (fun n hn => hann n (hsub hn))
  have hcells := card_floor_cells_le s (fun n : Fin 2 → ℤ => (n 0:ℝ)) hL hT hproj
  calc
    _ = ∑ k ∈ s.image f, ((s.filter (fun n => f n = k)).card:ℝ) := by
      rw [Finset.card_eq_sum_card_image f s,Nat.cast_sum]
    _ ≤ ∑ _k ∈ s.image f, 8*Real.sqrt (Q*rho) := Finset.sum_le_sum (fun k _ => hfiber k)
    _ = ((s.image f).card:ℝ)*(8*Real.sqrt (Q*rho)) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcells (by positivity)

/-- Optimizing the chart subdivision gives exactly the elementary branch's
three terms, with radius parametrized as `r³`. -/
theorem card_annulus_chart_le_optimized (s : Finset (Fin 2 → ℤ))
    {r rho c₀ c₁ d L : ℝ}
    (hr : 0 < r) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ r^3) (hscale : 1 ≤ r^3*rho)
    (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, r^3/4 ≤ (n 1:ℝ)-c₁)
    (hhorizontal : ∀ n ∈ s, |(n 0:ℝ)-c₀| ≤ 2*r^3)
    (hproj : ∀ n ∈ s, |(n 0:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  obtain ⟨T,hT,hthin,hrecip⟩ := exists_annulus_cell_width hr hrho
  have hc := card_annulus_chart_le s (pow_pos hr 3) hrho hrhoQ hscale hT hL
    hchart hhorizontal hproj hann hthin
  have hid : 2*L/T+2 = 20000*(L/r+L*rho)+2 := by
    rw [div_eq_mul_one_div,hrecip]
    ring
  rw [hid] at hc
  have hcoef : (20000*(L/r+L*rho)+2)*8 ≤ 160000*(1+L*rho+L/r) := by
    linarith only
  calc
    _ ≤ (20000*(L/r+L*rho)+2)*(8*Real.sqrt (r^3*rho)) := hc
    _ = ((20000*(L/r+L*rho)+2)*8)*Real.sqrt (r^3*rho) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- Transfer the chart estimate through an actual injective lattice-coordinate
map. Applied below only to the four quarter-turn rotations. -/
theorem card_annulus_chart_le_optimized_map (s : Finset (Fin 2 → ℤ))
    (e : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ)) {r rho c₀ c₁ d L : ℝ}
    (hr : 0 < r) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ r^3) (hscale : 1 ≤ r^3*rho)
    (hL : 0 ≤ L)
    (hchart : ∀ n ∈ s, r^3/4 ≤ (e n 1:ℝ)-c₁)
    (hhorizontal : ∀ n ∈ s, |(e n 0:ℝ)-c₀| ≤ 2*r^3)
    (hproj : ∀ n ∈ s, |(e n 0:ℝ)-d| ≤ L)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((e n 0:ℝ)-c₀)^2+((e n 1:ℝ)-c₁)^2)-r^3| ≤ rho) :
    (s.card:ℝ) ≤ 160000*(1+L*rho+L/r)*Real.sqrt (r^3*rho) := by
  classical
  have hc := card_annulus_chart_le_optimized (s.map e) hr hrho hrhoQ hscale hL
    (by intro n hn; obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn; exact hchart q hq)
    (by intro n hn; obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn; exact hhorizontal q hq)
    (by intro n hn; obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn; exact hproj q hq)
    (by intro n hn; obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hn; exact hann q hq)
  simpa only [Finset.card_map] using hc

end WaveTurbulence.Counting
