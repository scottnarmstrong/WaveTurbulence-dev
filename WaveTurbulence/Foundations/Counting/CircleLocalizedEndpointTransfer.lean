/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleEndpointTransfer
public import WaveTurbulence.Foundations.Counting.CircleEndpointGeometry
public import WaveTurbulence.Foundations.Counting.AnnulusHalfRadius
import Mathlib.Tactic

/-!
# Localized endpoint estimates imply the complete source annulus bound

Only blocks satisfying the actual circle-source localization condition are
analytic inputs. The other blocks are proved empty. The downstream circle
and full half-radius annulus estimates retain all source terms and boundaries.
-/

public section

namespace WaveTurbulence.Counting

/-- Circle transfer assuming local estimates only on blocks satisfying the
shared B-process localization condition `3U<=R`. -/
theorem abs_card_latticeDisc_sub_area_le_of_localized_endpoint_power_bounds
    (c : EuclideanSpace ℝ (Fin 2)) {R C kappa lambda : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hblock : ∀ j : Fin 2, ∀ n : ℕ, 0 < n → ∀ m : ℕ, 1 ≤ R/(2:ℝ)^(m+1) → 3*(R/(2:ℝ)^(m+1)) ≤ R →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter (fun x : ℤ =>
        R/Real.sqrt 2 < |(x:ℝ)-c j| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c j| ∧
          R-|(x:ℝ)-c j| ≤ R/(2:ℝ)^m),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          C*(n:ℝ)^kappa*R^(kappa/2)*(R/(2:ℝ)^(m+1))^(lambda-kappa/2)) :
    |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤
      (2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*
        (6+C/((2:ℝ)^(lambda-kappa/2)-1)))*R^((kappa+lambda)/(1+kappa)) := by
  apply abs_card_latticeDisc_sub_area_le_of_endpoint_power_bounds c hR hC hk hk1 hl0 hl1
  intro j n hn m hm
  rcases circle_endpoint_block_empty_or_source_range (zero_lt_one.trans_le hR) m (c := c j) with he | hrange
  · rw [he,Finset.sum_empty,norm_zero]
    positivity
  · exact hblock j n hn m hm hrange

/-- The complete two-branch source annulus bound from actual localized
endpoint estimates, with no artificial quarter-radius thickness restriction. -/
theorem card_annulus_disc_le_min_of_localized_endpoint_power_bounds
    (s : Finset (Fin 2 → ℤ)) (c d : EuclideanSpace ℝ (Fin 2))
    {Q rho L C kappa lambda : ℝ}
    (hQ : 0 < Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/2) (hscale : 1 ≤ Q*rho)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hblock : ∀ R : ℝ, 1 ≤ R → ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ∀ m : ℕ, 1 ≤ R/(2:ℝ)^(m+1) → 3*(R/(2:ℝ)^(m+1)) ≤ R →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter (fun x : ℤ =>
        R/Real.sqrt 2 < |(x:ℝ)-c j| ∧ R/(2:ℝ)^(m+1) < R-|(x:ℝ)-c j| ∧
          R-|(x:ℝ)-c j| ≤ R/(2:ℝ)^m),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤
          C*(n:ℝ)^kappa*R^(kappa/2)*(R/(2:ℝ)^(m+1))^(lambda-kappa/2))
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hball : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ min ((9*Real.pi)*(Q*rho)+
      (3*(2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*
        (6+C/((2:ℝ)^(lambda-kappa/2)-1))))*Q^((kappa+lambda)/(1+kappa)))
      (640000*(Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
        L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3)))) := by
  have he := circle_frequency_exponent_mem_Icc hk hl0 hl1
  have hden : 0 < 1-kappa := sub_pos.mpr hk1
  have ha : 0 < lambda-kappa/2 := by linarith only [hk1,hl0]
  have hp : 0 < (2:ℝ)^(lambda-kappa/2)-1 := sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha)
  have hconst : 0 ≤ 2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*
      (6+C/((2:ℝ)^(lambda-kappa/2)-1)) := by positivity
  apply card_annulus_disc_le_min_of_circle_error_half_radius s c d hQ hrho hrhoQ hscale
    hL hconst ((by norm_num : (0:ℝ) ≤ 1/2).trans he.1) he.2 _ hann hball
  intro R hR
  exact abs_card_latticeDisc_sub_area_le_of_localized_endpoint_power_bounds c hR hC hk hk1 hl0 hl1
    (hblock R hR)

end WaveTurbulence.Counting
