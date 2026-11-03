/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.AnnulusDiscrepancy
import Mathlib.Tactic

/-!
# The circle-error annulus bound over the full source radius range

The elementary annulus assumptions allow thickness up to half the radius.
For thickness at least a quarter of the radius, the outer-disc estimate is
absorbed by the area term. Smaller thickness uses the proved strict-inner-
disc subtraction. Thus the artificial quarter-radius restriction disappears.
-/

public section

namespace WaveTurbulence.Counting

/-- The general circle-error annulus branch under the same radius and
thickness assumptions as the source elementary branch, including closed
boundaries and the bounded-radius range. -/
theorem card_annulus_le_of_circle_error_half_radius (s : Finset (Fin 2 → ℤ))
    (c : EuclideanSpace ℝ (Fin 2)) {Q rho C e : ℝ}
    (hQ : 0 < Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/2) (hscale : 1 ≤ Q*rho)
    (hC : 0 ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdisc : ∀ R : ℝ, 1 ≤ R → |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ C*R^e)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho) :
    (s.card:ℝ) ≤ (9*Real.pi)*(Q*rho)+(3*C)*Q^e := by
  classical
  have hprod := mul_le_mul_of_nonneg_left hrhoQ hQ.le
  have hQ1 : 1 ≤ Q := by nlinarith only [hscale,hprod,hQ]
  by_cases hsmall : rho ≤ Q/4
  · have hp := mul_le_mul_of_nonneg_left hsmall hQ.le
    have hQ2 : 2 ≤ Q := by nlinarith only [hscale,hp,hQ]
    have hh := card_annulus_le_of_circle_error s c hQ2 hrho hsmall hC he0 he1 hdisc hann
    apply hh.trans
    have hpos : 0 ≤ Real.pi*(Q*rho) := by positivity
    nlinarith only [hpos]
  · have hR1 : 1 ≤ Q+rho := by linarith only [hQ1,hrho]
    have hsub : s ⊆ latticeDisc c (Q+rho) := by
      intro n hn
      apply (mem_latticeDisc (by linarith only [hR1] : 0 ≤ Q+rho)).mpr
      have hh := (abs_le.mp (hann n hn)).2
      linarith only [hh]
    have hcard : (s.card:ℝ) ≤ ((latticeDisc c (Q+rho)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have herr := (le_abs_self (((latticeDisc c (Q+rho)).card:ℝ)-Real.pi*(Q+rho)^2)).trans
      (hdisc (Q+rho) hR1)
    have hpow : (Q+rho)^e ≤ 2*Q^e := by
      calc
        _ ≤ (2*Q)^e := Real.rpow_le_rpow (by positivity) (by linarith only [hrhoQ,hQ]) he0
        _ = (2:ℝ)^e*Q^e := Real.mul_rpow (by norm_num) hQ.le
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ) ≤ 2) he1) (Real.rpow_nonneg hQ.le _)
    have hsquare : (Q+rho)^2 ≤ (3*Q/2)^2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith only [hrhoQ])
    have hQsq : Q^2 ≤ 4*Q*rho := by
      have hp := mul_le_mul_of_nonneg_left (le_of_not_ge hsmall) hQ.le
      nlinarith only [hp]
    have harea : Real.pi*(Q+rho)^2 ≤ (9*Real.pi)*(Q*rho) := by
      have hs : (Q+rho)^2 ≤ 9*(Q*rho) := by nlinarith only [hsquare,hQsq]
      have hp := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
      nlinarith only [hp]
    have herror := mul_le_mul_of_nonneg_left hpow hC
    have hnonneg : 0 ≤ C*Q^e := by positivity
    nlinarith only [hcard,herr,harea,herror,hnonneg]

/-- Both complete source annulus branches, with the general circle error,
under the full half-radius thickness range. -/
theorem card_annulus_disc_le_min_of_circle_error_half_radius (s : Finset (Fin 2 → ℤ))
    (c d : EuclideanSpace ℝ (Fin 2)) {Q rho L C e : ℝ}
    (hQ : 0 < Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/2) (hscale : 1 ≤ Q*rho)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdisc : ∀ R : ℝ, 1 ≤ R → |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ C*R^e)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hball : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ min ((9*Real.pi)*(Q*rho)+(3*C)*Q^e)
      (640000*(Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
        L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3)))) := by
  exact le_min (card_annulus_le_of_circle_error_half_radius s c hQ hrho hrhoQ hscale
    hC he0 he1 hdisc hann)
    (card_annulus_disc_le_expanded s c d hQ hrho.le hrhoQ hscale hL hann hball)

end WaveTurbulence.Counting
