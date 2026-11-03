/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleOctantError
public import WaveTurbulence.Foundations.Counting.CircleCapSmoothing
public import WaveTurbulence.Foundations.Counting.CircleExponentTransfer
import Mathlib.Tactic

/-!
# Conditional exponent transfer through the outer octants

Only the outer-octant frequency estimates are hypotheses. The central
square, artificial edges, translated centers, circular boundaries, area,
and smoothing cutoff are all handled by proved lemmas. The shared VdCB
exponent-pair predicate is not redefined here.
-/

public section

namespace WaveTurbulence.Counting

/-- Conditional outer-octant frequency transfer at radius at least two.
The exponent is exactly `(kappa+lambda)/(1+kappa)`. -/
theorem abs_card_latticeDisc_sub_area_le_of_outer_cap_frequency_scale_two
    (c : EuclideanSpace ℝ (Fin 2)) {R C kappa lambda : ℝ}
    (hR : 2 ≤ R) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hfreq : ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter
          (fun x : ℤ => R/Real.sqrt 2 < |(x:ℝ)-c j|),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          (C*R^lambda)*(n:ℝ)^kappa) :
    |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤
      (83+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*R^((kappa+lambda)/(1+kappa)) := by
  let e : ℝ := (kappa+lambda)/(1+kappa)
  let D : ℝ := (3:ℝ)/2+2*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C
  have hR1 : 1 ≤ R := by linarith only [hR]
  have he := circle_frequency_exponent_mem_Icc hk hl0 hl1
  have hhalf : (1:ℝ)/2 ≤ e := he.1
  have he0 : 0 ≤ e := (by norm_num : (0:ℝ) ≤ 1/2).trans hhalf
  have hone : 1 ≤ R^e := Real.one_le_rpow hR1 he0
  have hsqrt : Real.sqrt R ≤ R^e := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hR1 hhalf
  have hpsi (j : Fin 2) (d : ℝ) :
      |circleCapSawtooth R (R/Real.sqrt 2) (c j) d| ≤ D*R^e :=
    circle_cap_sawtooth_le_of_frequency_scale hR1 hC hk hk1 hl1 (hfreq j)
  have hb := abs_card_latticeDisc_sub_area_le_outer_sawtooth c hR
  calc
    _ ≤ 60*Real.sqrt R+17+
        |circleCapSawtooth R (R/Real.sqrt 2) (c 0) (c 1)|+
        |circleCapSawtooth R (R/Real.sqrt 2) (c 0) (-c 1)|+
        |circleCapSawtooth R (R/Real.sqrt 2) (c 1) (c 0)|+
        |circleCapSawtooth R (R/Real.sqrt 2) (c 1) (-c 0)| := hb
    _ ≤ 77*R^e+4*D*R^e := by
      linarith only [hsqrt,hone,hpsi 0 (c 1),hpsi 0 (-c 1),hpsi 1 (c 0),hpsi 1 (-c 0)]
    _ = _ := by dsimp only [D,e]; ring

/-- The same outer-octant transfer for every radius at least one. The
bounded small-radius range is covered by the proved elementary discrepancy. -/
theorem abs_card_latticeDisc_sub_area_le_of_outer_cap_frequency_scale
    (c : EuclideanSpace ℝ (Fin 2)) {R C kappa lambda : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hfreq : ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter
          (fun x : ℤ => R/Real.sqrt 2 < |(x:ℝ)-c j|),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          (C*R^lambda)*(n:ℝ)^kappa) :
    |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤
      (2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*R^((kappa+lambda)/(1+kappa)) := by
  have hden : 0 < 1-kappa := sub_pos.mpr hk1
  have hB : 0 ≤ ((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C := by positivity
  by_cases hR2 : 2 ≤ R
  · exact (abs_card_latticeDisc_sub_area_le_of_outer_cap_frequency_scale_two
      c hR2 hC hk hk1 hl0 hl1 hfreq).trans
      (mul_le_mul_of_nonneg_right (by linarith only) (Real.rpow_nonneg (le_trans zero_le_one hR) _))
  · have he := circle_frequency_exponent_mem_Icc hk hl0 hl1
    have hone : 1 ≤ R^((kappa+lambda)/(1+kappa)) :=
      Real.one_le_rpow hR ((by norm_num : (0:ℝ) ≤ 1/2).trans he.1)
    have hpow : R^((2:ℝ)/3) ≤ 2 :=
      (Real.rpow_le_self_of_one_le hR (by norm_num : (2:ℝ)/3 ≤ 1)).trans (le_of_not_ge hR2)
    have hconst : 0 ≤ 2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C := by
      nlinarith only [hB]
    calc
      _ ≤ 1334*R^((2:ℝ)/3) := abs_card_latticeDisc_sub_area_le hR c
      _ ≤ 2668 := by linarith only [hpow]
      _ ≤ 2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C := by nlinarith only [hB]
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hconst

end WaveTurbulence.Counting
