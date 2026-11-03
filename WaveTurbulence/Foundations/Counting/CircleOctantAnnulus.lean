/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleOctantTransfer
public import WaveTurbulence.Foundations.Counting.AnnulusDiscrepancy
import Mathlib.Tactic

/-!
# Conditional outer-octant transfer to the full annulus bound

NT-EXPSUM: the local frequency hypothesis remains explicit until VdCB's
shared `IsExponentPair` API supplies it. The geometric annulus comparison
and the complete elementary branch are proved, including closed boundaries.
-/

public section

namespace WaveTurbulence.Counting

/-- Uniform outer-cap frequency bounds supplies the annulus error with
`e=(kappa+lambda)/(1+kappa)`. This is a distinct conditional helper. -/
theorem card_annulus_le_of_outer_cap_frequency_scale (s : Finset (Fin 2 → ℤ))
    (c : EuclideanSpace ℝ (Fin 2)) {Q rho C kappa lambda : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4)
    (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hfreq : ∀ R : ℝ, 1 ≤ R → ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter
          (fun x : ℤ => R/Real.sqrt 2 < |(x:ℝ)-c j|),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤ (C*R^lambda)*(n:ℝ)^kappa)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho) :
    (s.card:ℝ) ≤ (6*Real.pi)*(Q*rho)+
      (3*(2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C))*
        Q^((kappa+lambda)/(1+kappa)) := by
  have he := circle_frequency_exponent_mem_Icc hk hl0 hl1
  have hden : 0 < 1-kappa := sub_pos.mpr hk1
  have hconst : 0 ≤ 2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C := by positivity
  apply card_annulus_le_of_circle_error s c hQ hrho hrhoQ hconst
    ((by norm_num : (0:ℝ) ≤ 1/2).trans he.1) he.2
  · intro R hR
    exact abs_card_latticeDisc_sub_area_le_of_outer_cap_frequency_scale c hR hC hk hk1 hl0 hl1 (hfreq R hR)
  · exact hann

/-- Both source annulus branches under the explicit outer-cap frequency
hypothesis; the second branch is unconditional and fully geometric. -/
theorem card_annulus_disc_le_min_of_outer_cap_frequency_scale (s : Finset (Fin 2 → ℤ))
    (c d : EuclideanSpace ℝ (Fin 2)) {Q rho L C kappa lambda : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4) (hscale : 1 ≤ Q*rho) (hL : 0 ≤ L)
    (hC : 0 ≤ C) (hk : 0 < kappa) (hk1 : kappa < 1)
    (hl0 : (1:ℝ)/2 ≤ lambda) (hl1 : lambda ≤ 1)
    (hfreq : ∀ R : ℝ, 1 ≤ R → ∀ j : Fin 2, ∀ n : ℕ, 0 < n →
      ‖∑ x ∈ (integerInterval (c j-R) (c j+R)).filter
          (fun x : ℤ => R/Real.sqrt 2 < |(x:ℝ)-c j|),
        NumberTheory.expPhase ((n:ℝ)*circleHeight R (c j) x)‖ ≤ (C*R^lambda)*(n:ℝ)^kappa)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hball : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ min ((6*Real.pi)*(Q*rho)+
        (3*(2668+8*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C))*Q^((kappa+lambda)/(1+kappa)))
      (640000*(Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
        L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3)))) := by
  apply le_min
  · exact card_annulus_le_of_outer_cap_frequency_scale s c hQ hrho hrhoQ hC hk hk1 hl0 hl1 hfreq hann
  · exact card_annulus_disc_le_expanded s c d (by linarith only [hQ]) hrho.le
      (by linarith only [hQ,hrhoQ]) hscale hL hann hball

end WaveTurbulence.Counting
