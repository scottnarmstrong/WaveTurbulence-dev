/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.QuadraticStrip
public import WaveTurbulence.Foundations.Counting.LatticeTriangle
import Mathlib.Tactic

/-!
# Lattice points on lines in annuli

DH23 `basiccount0pre` (1), elementary branch, TeX L2042: a line contributes
`O(sqrt (Q*rho))` lattice points to an annulus of radius `Q` and width `rho`.
The squared-radius band formulation below avoids choices of open or closed
radial endpoints, and includes both components of the intersection.
-/

public section

namespace WaveTurbulence.Counting

/-- Restricting squared Euclidean distance to a nonvertical affine line gives
a quadratic with leading coefficient at least one. -/
theorem affine_graph_distance_sq (m b c₀ c₁ x : ℝ) :
    (x-c₀)^2+(m*x+b-c₁)^2 =
      (1+m^2)*(x-(c₀-m*(b-c₁))/(1+m^2))^2 +
      (c₀^2+(b-c₁)^2-(1+m^2)*((c₀-m*(b-c₁))/(1+m^2))^2) := by
  have hA : 1+m^2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- Integer points on an affine graph in a squared-radius annulus satisfy a
square-root count, uniformly in its center and in the slope of the line. -/
theorem card_affine_graph_annulus_le (s : Finset (Fin 2 → ℤ))
    {m b c₀ c₁ K W : ℝ} (hW : 0 ≤ W)
    (hgraph : ∀ n ∈ s, (n 1:ℝ) = m*(n 0:ℝ)+b)
    (hband : ∀ n ∈ s, |((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2-K| ≤ W) :
    (s.card:ℝ) ≤ 2*Real.sqrt (2*W)+2 := by
  classical
  have hinj : Set.InjOn (fun n : Fin 2 → ℤ => n 0) (s : Set (Fin 2 → ℤ)) := by
    intro x hx y hy he
    dsimp only at he
    have hx' := hgraph x hx
    have hy' := hgraph y hy
    rw [he] at hx'
    have h₁ : x 1 = y 1 := by exact_mod_cast hx'.trans hy'.symm
    ext i
    fin_cases i
    · exact he
    · exact h₁
  have hc := Finset.card_image_of_injOn hinj
  rw [← hc]
  apply card_quadratic_strip_le _ (show 1 ≤ 1+m^2 by nlinarith only [sq_nonneg m]) hW
  intro k hk
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
  have hb := hband n hn
  rw [hgraph n hn, affine_graph_distance_sq] at hb
  exact hb

/-- Radial annulus membership gives a squared-radius band of width
`rho * (2*Q+rho)`. -/
theorem abs_sq_sub_sq_le_of_abs_sub_le {a Q rho : ℝ}
    (ha : 0 ≤ a) (hQ : 0 ≤ Q) (hrho : 0 ≤ rho) (h : |a-Q| ≤ rho) :
    |a^2-Q^2| ≤ rho*(2*Q+rho) := by
  have hup : a ≤ Q+rho := by
    have hh := le_abs_self (a-Q)
    linarith only [hh,h]
  rw [show a^2-Q^2 = (a-Q)*(a+Q) by ring, abs_mul,
    abs_of_nonneg (add_nonneg ha hQ)]
  exact mul_le_mul h (by linarith only [hup]) (add_nonneg ha hQ) hrho

/-- A nonvertical line contributes at most `8 * sqrt (Q*rho)` integer points
to the annulus `abs (distance-Q) ≤ rho`, under the source scale assumptions. -/
theorem card_affine_graph_radial_annulus_le (s : Finset (Fin 2 → ℤ))
    {m b c₀ c₁ Q rho : ℝ} (hQ : 0 ≤ Q) (hrho : 0 ≤ rho)
    (hrhoQ : rho ≤ Q) (hscale : 1 ≤ Q*rho)
    (hgraph : ∀ n ∈ s, (n 1:ℝ) = m*(n 0:ℝ)+b)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-Q| ≤ rho) :
    (s.card:ℝ) ≤ 8*Real.sqrt (Q*rho) := by
  have hband : ∀ n ∈ s,
      |((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2-Q^2| ≤ rho*(2*Q+rho) := by
    intro n hn
    have hb := abs_sq_sub_sq_le_of_abs_sub_le (Real.sqrt_nonneg _) hQ hrho (hann n hn)
    rw [Real.sq_sqrt (by positivity)] at hb
    exact hb
  have hc := card_affine_graph_annulus_le s (by positivity : 0 ≤ rho*(2*Q+rho)) hgraph hband
  have hprod : 0 ≤ Q*rho := mul_nonneg hQ hrho
  have hW : rho*(2*Q+rho) ≤ 3*(Q*rho) := by
    have hm := mul_nonneg hrho (sub_nonneg.mpr hrhoQ)
    nlinarith only [hm]
  have hs : Real.sqrt (2*(rho*(2*Q+rho))) ≤ 3*Real.sqrt (Q*rho) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have he := Real.sq_sqrt hprod
      nlinarith only [he,hW,hprod]
  have hone : 1 ≤ Real.sqrt (Q*rho) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hscale
  linarith only [hc,hs,hone]

/-- The radial line estimate is invariant under exchanging the two integer
coordinates, so vertical lines are covered as well. -/
theorem card_affine_graph_radial_annulus_le_swap (s : Finset (Fin 2 → ℤ))
    {m b c₀ c₁ Q rho : ℝ} (hQ : 0 ≤ Q) (hrho : 0 ≤ rho)
    (hrhoQ : rho ≤ Q) (hscale : 1 ≤ Q*rho)
    (hgraph : ∀ n ∈ s, (n 0:ℝ) = m*(n 1:ℝ)+b)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-Q| ≤ rho) :
    (s.card:ℝ) ≤ 8*Real.sqrt (Q*rho) := by
  classical
  let e : (Fin 2 → ℤ) ↪ (Fin 2 → ℤ) :=
    ⟨fun n => ![n 1,n 0], by
      intro x y he
      have h0 := congrFun he 1
      have h1 := congrFun he 0
      ext i
      fin_cases i
      · exact h0
      · exact h1⟩
  have hc := card_affine_graph_radial_annulus_le (s.map e)
    (m := m) (b := b) (c₀ := c₁) (c₁ := c₀) hQ hrho hrhoQ hscale
    (by
      intro n hn
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hn
      change (r 0:ℝ) = m*(r 1:ℝ)+b
      exact hgraph r hr)
    (by
      intro n hn
      obtain ⟨r,hr,rfl⟩ := Finset.mem_map.mp hn
      change |Real.sqrt (((r 1:ℝ)-c₁)^2+((r 0:ℝ)-c₀)^2)-Q| ≤ rho
      rw [add_comm]
      exact hann r hr)
  simpa only [Finset.card_map] using hc

/-- DH23's elementary annulus argument: a collinear lattice subset of the
annulus has `O(sqrt (Q*rho))` points. Degeneracy is stated by the exact integer
triangle determinant, with no restrictions on the direction of its line. -/
theorem card_collinear_radial_annulus_le (s : Finset (Fin 2 → ℤ))
    {c₀ c₁ Q rho : ℝ} (hQ : 0 ≤ Q) (hrho : 0 ≤ rho)
    (hrhoQ : rho ≤ Q) (hscale : 1 ≤ Q*rho)
    (hdet : ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, latticeTriangleDet p q r = 0)
    (hann : ∀ n ∈ s,
      |Real.sqrt (((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2)-Q| ≤ rho) :
    (s.card:ℝ) ≤ 8*Real.sqrt (Q*rho) := by
  classical
  by_cases hs : s.card ≤ 1
  · have hc : (s.card:ℝ) ≤ 1 := by exact_mod_cast hs
    have hh : 1 ≤ Real.sqrt (Q*rho) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hscale
    linarith only [hc,hh]
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hs)
  by_cases hx : q 0-p 0 ≠ 0
  · obtain ⟨m,b,hg⟩ := exists_affine_graph_of_triangleDet_eq_zero s p q hx (hdet p hp q hq)
    exact card_affine_graph_radial_annulus_le s hQ hrho hrhoQ hscale hg hann
  · have hx0 : q 0-p 0 = 0 := not_ne_iff.mp hx
    have hy : q 1-p 1 ≠ 0 := by
      intro he
      apply hpq
      ext i
      fin_cases i
      · exact (sub_eq_zero.mp hx0).symm
      · exact (sub_eq_zero.mp he).symm
    have hg : ∀ r ∈ s, (r 0:ℝ) = (0:ℝ)*(r 1:ℝ)+(p 0:ℝ) := by
      intro r hr
      have hd := hdet p hp q hq r hr
      simp only [latticeTriangleDet,latticeDet,Pi.sub_apply,hx0,zero_mul,zero_sub,neg_eq_zero] at hd
      have he : r 0 = p 0 := sub_eq_zero.mp ((mul_eq_zero.mp hd).resolve_left hy)
      simp only [zero_mul,zero_add,he]
    exact card_affine_graph_radial_annulus_le_swap s hQ hrho hrhoQ hscale hg hann

end WaveTurbulence.Counting
