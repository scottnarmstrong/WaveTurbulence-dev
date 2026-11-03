/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointFrequency
public import WaveTurbulence.Foundations.Counting.CircleOctantAnnulus
import Mathlib.Tactic

/-!
# Local endpoint power bounds imply circle discrepancy

This distinct conditional helper consumes the actual dyadic endpoint-block
exponential sums. The geometric block summation, outer-octant reduction,
area, closed boundaries and optimized sawtooth smoothing are all proved.
The shared VdCB phase-class application remains the only analytic input.
-/

public section

namespace WaveTurbulence.Counting

private theorem endpoint_frequency_constant_nonneg {C kappa lambda : ℝ}
    (hC : 0 ≤ C) (hk1 : kappa < 1) (hl : (1:ℝ)/2 ≤ lambda) :
    0 ≤ 6+C/((2:ℝ)^(lambda-kappa/2)-1) := by
  have ha : 0 < lambda-kappa/2 := by linarith only [hk1,hl]
  have hd : 0 < (2:ℝ)^(lambda-kappa/2)-1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha)
  positivity

/-- Actual local dyadic endpoint estimates imply the uniform translated
closed-disc error at exponent `(kappa+lambda)/(1+kappa)`. This theorem does
not assert that those local analytic estimates hold unconditionally. -/
theorem abs_card_latticeDisc_sub_area_le_of_endpoint_power_bounds
    (c : EuclideanSpace ℝ (Fin 2)) {R C kappa lambda : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hblock : ∀ j : Fin 2, ∀ n : ℕ, 0 < n → ∀ m : ℕ, 1 ≤ R/(2:ℝ)^(m+1) →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter (fun x : ℤ =>
        R/Real.sqrt 2 < |(x:ℝ)-c j| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c j| ∧
          R-|(x:ℝ)-c j| ≤ R/(2:ℝ)^m),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          C*(n:ℝ)^kappa*R^(kappa/2)*(R/(2:ℝ)^(m+1))^(lambda-kappa/2)) :
    |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤
      (2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*
        (6+C/((2:ℝ)^(lambda-kappa/2)-1)))*R^((kappa+lambda)/(1+kappa)) := by
  apply abs_card_latticeDisc_sub_area_le_of_outer_cap_frequency_scale c hR
    (endpoint_frequency_constant_nonneg hC hk1 hl0) hk hk1 hl0 hl1
  intro j n hn
  exact circle_outer_cap_exp_sum_le_of_endpoint_power_bounds hR hC hk.le hk1 hl0 n hn (hblock j n hn)

/-- The same actual local block estimates, uniformly in radius, give the
annulus error branch with the improved exponent. -/
theorem card_annulus_le_of_endpoint_power_bounds (s : Finset (Fin 2 → ℤ))
    (c : EuclideanSpace ℝ (Fin 2)) {Q rho C kappa lambda : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4)
    (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hblock : ∀ R : ℝ, 1 ≤ R → ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ∀ m : ℕ, 1 ≤ R/(2:ℝ)^(m+1) →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter (fun x : ℤ =>
        R/Real.sqrt 2 < |(x:ℝ)-c j| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c j| ∧
          R-|(x:ℝ)-c j| ≤ R/(2:ℝ)^m),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          C*(n:ℝ)^kappa*R^(kappa/2)*(R/(2:ℝ)^(m+1))^(lambda-kappa/2))
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho) :
    (s.card:ℝ) ≤ (6*Real.pi)*(Q*rho)+
      (3*(2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*
        (6+C/((2:ℝ)^(lambda-kappa/2)-1))))*Q^((kappa+lambda)/(1+kappa)) := by
  apply card_annulus_le_of_outer_cap_frequency_scale s c hQ hrho hrhoQ
    (endpoint_frequency_constant_nonneg hC hk1 hl0) hk hk1 hl0 hl1 _ hann
  intro R hR j n hn
  exact circle_outer_cap_exp_sum_le_of_endpoint_power_bounds hR hC hk.le hk1 hl0 n hn (hblock R hR j n hn)

end WaveTurbulence.Counting
