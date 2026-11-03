/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeTriangle
import Mathlib.Tactic

/-!
# Thin annulus sections in Cartesian charts

DH23 `basiccount0pre` (1), elementary branch: on a chart where the vertical
coordinate is bounded below by a fixed fraction of the radius, a short
horizontal interval produces a thin box in the tangent frame. Cartesian
charts avoid angular endpoint choices in the annulus covering.
-/

public section

namespace WaveTurbulence.Counting

/-- Two points in the same upper annulus chart have controlled vertical
separation in terms of their horizontal separation and the annulus width. -/
theorem annulus_chart_vertical_difference_le {Q rho T K u v x y : ℝ}
    (hQ : 0 < Q) (hT : 0 ≤ T)
    (hv : Q/4 ≤ v) (hy : Q/4 ≤ y)
    (hu : |u| ≤ 2*Q) (hx : |x| ≤ 2*Q) (hdx : |x-u| ≤ T)
    (hp : |u^2+v^2-K| ≤ 3*Q*rho) (hq : |x^2+y^2-K| ≤ 3*Q*rho) :
    |y-v| ≤ 12*rho+8*T := by
  have hnorm : |(x^2+y^2)-(u^2+v^2)| ≤ 6*Q*rho := by
    have hp' := abs_le.mp hp
    have hq' := abs_le.mp hq
    apply abs_le.mpr
    constructor <;> linarith only [hp'.1,hp'.2,hq'.1,hq'.2]
  have hsum : |x+u| ≤ 4*Q := by
    have hu' := abs_le.mp hu
    have hx' := abs_le.mp hx
    apply abs_le.mpr
    constructor <;> linarith only [hu'.1,hu'.2,hx'.1,hx'.2]
  have hhor : |(x-u)*(x+u)| ≤ T*(4*Q) := by
    rw [abs_mul]
    exact mul_le_mul hdx hsum (abs_nonneg _) hT
  have hid : (y-v)*(y+v) = ((x^2+y^2)-(u^2+v^2))-(x-u)*(x+u) := by ring
  have hb : |(y-v)*(y+v)| ≤ 6*Q*rho+T*(4*Q) := by
    rw [hid]
    calc
      _ ≤ |(x^2+y^2)-(u^2+v^2)|+|(x-u)*(x+u)| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le ((x^2+y^2)-(u^2+v^2)) 0 ((x-u)*(x+u))
      _ ≤ _ := add_le_add hnorm hhor
  have hvy : Q/2 ≤ y+v := by linarith only [hv,hy]
  have hvy0 : 0 ≤ y+v := by linarith only [hQ,hvy]
  rw [abs_mul,abs_of_nonneg hvy0] at hb
  have hm := mul_le_mul_of_nonneg_left hvy (abs_nonneg (y-v))
  apply (mul_le_mul_iff_left₀ hQ).mp
  nlinarith only [hb,hm]

/-- An annulus chart of horizontal width `T` has thickness
`1000 * (rho + T²/Q)` in its tangent shear frame. -/
theorem annulus_chart_tangent_difference_le {Q rho T K u v x y : ℝ}
    (hQ : 0 < Q) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ Q) (hT : 0 ≤ T)
    (hv : Q/4 ≤ v) (hy : Q/4 ≤ y)
    (hu : |u| ≤ 2*Q) (hx : |x| ≤ 2*Q) (hdx : |x-u| ≤ T)
    (hp : |u^2+v^2-K| ≤ 3*Q*rho) (hq : |x^2+y^2-K| ≤ 3*Q*rho) :
    |(y-v)+(u/v)*(x-u)| ≤ 1000*(rho+T^2/Q) := by
  have hdy := annulus_chart_vertical_difference_le hQ hT hv hy hu hx hdx hp hq
  have hv0 : 0 < v := by linarith only [hQ,hv]
  have hid : 2*v*((y-v)+(u/v)*(x-u)) =
      ((x^2+y^2)-(u^2+v^2))-(x-u)^2-(y-v)^2 := by
    field_simp
    ring
  have hnorm : |(x^2+y^2)-(u^2+v^2)| ≤ 6*Q*rho := by
    have hp' := abs_le.mp hp
    have hq' := abs_le.mp hq
    apply abs_le.mpr
    constructor <;> linarith only [hp'.1,hp'.2,hq'.1,hq'.2]
  have hprod : |2*v*((y-v)+(u/v)*(x-u))| ≤ 6*Q*rho+(x-u)^2+(y-v)^2 := by
    rw [hid]
    have hn := abs_le.mp hnorm
    apply abs_le.mpr
    constructor <;> linarith only [hn.1,hn.2,sq_nonneg (x-u),sq_nonneg (y-v)]
  rw [abs_mul,abs_of_pos (by positivity : 0 < 2*v)] at hprod
  have hm := mul_le_mul_of_nonneg_right (by linarith only [hv] : Q/2 ≤ 2*v)
    (abs_nonneg ((y-v)+(u/v)*(x-u)))
  have hsx : (x-u)^2 ≤ T^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hdx 2
  have hsy : (y-v)^2 ≤ 288*rho^2+128*T^2 := by
    have he := pow_le_pow_left₀ (abs_nonneg _) hdy 2
    rw [sq_abs] at he
    nlinarith only [he,sq_nonneg (12*rho-8*T)]
  have hrhosq : rho^2 ≤ Q*rho := by
    have he := mul_nonneg hrho (sub_nonneg.mpr hrhoQ)
    nlinarith only [he]
  apply (mul_le_mul_iff_left₀ hQ).mp
  have he : (1000*(rho+T^2/Q))*Q = 1000*(Q*rho+T^2) := by
    field_simp
  rw [he]
  nlinarith only [hprod,hm,hsx,hsy,hrhosq]

/-- A sufficiently short annulus-chart section contains only degenerate
lattice triangles. All hypotheses describe its actual Cartesian geometry. -/
theorem lattice_annulus_chart_triangles_eq_zero (s : Finset (Fin 2 → ℤ))
    {Q rho T K c₀ c₁ : ℝ}
    (hQ : 0 < Q) (hrho : 0 ≤ rho) (hrhoQ : rho ≤ Q) (hT : 0 ≤ T)
    (hchart : ∀ n ∈ s, Q/4 ≤ (n 1:ℝ)-c₁)
    (hhorizontal : ∀ n ∈ s, |(n 0:ℝ)-c₀| ≤ 2*Q)
    (hwidth : ∀ p ∈ s, ∀ q ∈ s, |(q 0:ℝ)-(p 0:ℝ)| ≤ T)
    (hband : ∀ n ∈ s, |((n 0:ℝ)-c₀)^2+((n 1:ℝ)-c₁)^2-K| ≤ 3*Q*rho)
    (hthin : 2*T*(1000*(rho+T^2/Q)) < 1) :
    ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, latticeTriangleDet p q r = 0 := by
  intro p hp q hq r hr
  let u : ℝ := (p 0:ℝ)-c₀
  let v : ℝ := (p 1:ℝ)-c₁
  have hnormal (z : Fin 2 → ℤ) (hz : z ∈ s) :
      |(u/v)*((z 0-p 0:ℤ):ℝ)+((z 1-p 1:ℤ):ℝ)| ≤ 1000*(rho+T^2/Q) := by
    have hdx : |((z 0:ℝ)-c₀)-u| ≤ T := by
      have he : ((z 0:ℝ)-c₀)-u = (z 0:ℝ)-(p 0:ℝ) := by dsimp only [u]; ring
      rw [he]
      exact hwidth p hp z hz
    have hb := annulus_chart_tangent_difference_le hQ hrho hrhoQ hT
      (hchart p hp) (hchart z hz) (hhorizontal p hp) (hhorizontal z hz)
      hdx (hband p hp) (hband z hz)
    have he : (u/v)*((z 0-p 0:ℤ):ℝ)+((z 1-p 1:ℤ):ℝ) =
        (((z 1:ℝ)-c₁)-v)+(u/v)*(((z 0:ℝ)-c₀)-u) := by
      dsimp only [u,v]
      push_cast
      ring
    rw [he]
    exact hb
  apply latticeTriangleDet_eq_zero_of_thin_frame (a := 1) (b := 0)
    (c := u/v) (d := 1) (W := T) (T := 1000*(rho+T^2/Q))
  · ring
  · simpa only [one_mul,zero_mul,add_zero,Int.cast_sub] using hwidth p hp q hq
  · simpa only [one_mul,zero_mul,add_zero,Int.cast_sub] using hwidth p hp r hr
  · simpa only [one_mul] using hnormal q hq
  · simpa only [one_mul] using hnormal r hr
  · exact hthin

end WaveTurbulence.Counting
