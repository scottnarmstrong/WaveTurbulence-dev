/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CircleDiscrepancy
public import WaveTurbulence.Foundations.Counting.AnnulusElementary
import Mathlib.Tactic

/-!
# Annulus counts from a circle discrepancy exponent

The first branch of DH23 `basiccount0pre` (1), with a general exponent `e`.
The conditional helper is distinct from the unconditional two-thirds instance.
Closed annulus boundaries are retained: the inner comparison disc is separated
from the annulus by a positive gap rather than discarding its boundary points.
-/

public section

namespace WaveTurbulence.Counting

/-- A uniform closed-disc discrepancy estimate gives the annulus bound with
the same exponent. The inner comparison radius `Q-2*rho` avoids boundary loss. -/
theorem card_annulus_le_of_circle_error (s : Finset (Fin 2 → ℤ))
    (c : EuclideanSpace ℝ (Fin 2)) {Q rho C e : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4)
    (hC : 0 ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdisc : ∀ R : ℝ, 1 ≤ R →
      |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ C*R^e)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho) :
    (s.card:ℝ) ≤ (6*Real.pi)*(Q*rho)+(3*C)*Q^e := by
  classical
  have hQp : 0 < Q := by linarith only [hQ]
  have hout1 : 1 ≤ Q+rho := by linarith only [hQ,hrho]
  have hin1 : 1 ≤ Q-2*rho := by linarith only [hQ,hrhoQ]
  have hout0 : 0 ≤ Q+rho := le_trans zero_le_one hout1
  have hin0 : 0 ≤ Q-2*rho := le_trans zero_le_one hin1
  have hsub : s ∪ latticeDisc c (Q-2*rho) ⊆ latticeDisc c (Q+rho) := by
    intro n hn
    apply (mem_latticeDisc hout0).mpr
    rcases Finset.mem_union.mp hn with hn | hn
    · have hh := (abs_le.mp (hann n hn)).2
      linarith only [hh]
    · have hh := (mem_latticeDisc hin0).mp hn
      linarith only [hh,hrho]
  have hdisj : Disjoint s (latticeDisc c (Q-2*rho)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    have hlow := (abs_le.mp (hann n hn)).1
    have hhigh := (mem_latticeDisc hin0).mp hm
    linarith only [hlow,hhigh,hrho]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hc
  have hcR : (s.card:ℝ)+((latticeDisc c (Q-2*rho)).card:ℝ) ≤
      ((latticeDisc c (Q+rho)).card:ℝ) := by exact_mod_cast hc
  have hout := (abs_le.mp (hdisc (Q+rho) hout1)).2
  have hin := (abs_le.mp (hdisc (Q-2*rho) hin1)).1
  have houtle := sub_le_iff_le_add.mp hout
  have hinle : -C*(Q-2*rho)^e+Real.pi*(Q-2*rho)^2 ≤
      ((latticeDisc c (Q-2*rho)).card:ℝ) := by
    simpa only [neg_mul] using le_sub_iff_add_le.mp hin
  have hinner : (Q-2*rho)^e ≤ Q^e :=
    Real.rpow_le_rpow hin0 (by linarith only [hrho]) he0
  have htwo : (2:ℝ)^e ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he1
  have houter : (Q+rho)^e ≤ 2*Q^e := by
    calc
      _ ≤ (2*Q)^e := Real.rpow_le_rpow hout0 (by linarith only [hQp,hrhoQ]) he0
      _ = (2:ℝ)^e*Q^e := Real.mul_rpow (by norm_num) hQp.le
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hQp.le _)
  have hsum : (Q+rho)^e+(Q-2*rho)^e ≤ 3*Q^e := by
    calc
      _ ≤ 2*Q^e+Q^e := add_le_add houter hinner
      _ = _ := by ring
  have harea : 6*Q*rho-3*rho^2 ≤ 6*Q*rho := by nlinarith only [sq_nonneg rho]
  calc
    _ ≤ ((latticeDisc c (Q+rho)).card:ℝ)-((latticeDisc c (Q-2*rho)).card:ℝ) :=
      le_sub_iff_add_le.mpr hcR
    _ ≤ (C*(Q+rho)^e+Real.pi*(Q+rho)^2)-(-C*(Q-2*rho)^e+Real.pi*(Q-2*rho)^2) :=
      sub_le_sub houtle hinle
    _ = Real.pi*(6*Q*rho-3*rho^2)+C*((Q+rho)^e+(Q-2*rho)^e) := by ring
    _ ≤ Real.pi*(6*Q*rho)+C*(3*Q^e) := add_le_add
      (mul_le_mul_of_nonneg_left harea Real.pi_pos.le) (mul_le_mul_of_nonneg_left hsum hC)
    _ = _ := by ring

/-- Unconditional first annulus branch using the proved uniform two-thirds
circle discrepancy. No Huxley estimate is imported or assumed. -/
theorem card_annulus_le_two_thirds (s : Finset (Fin 2 → ℤ))
    (c : EuclideanSpace ℝ (Fin 2)) {Q rho : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho) :
    (s.card:ℝ) ≤ (6*Real.pi)*(Q*rho)+4002*Q^((2:ℝ)/3) := by
  simpa only [show (3:ℝ)*1334 = 4002 by norm_num] using
    card_annulus_le_of_circle_error s c hQ hrho hrhoQ
    (by norm_num : (0:ℝ) ≤ 1334) (by norm_num : (0:ℝ) ≤ 2/3) (by norm_num : (2:ℝ)/3 ≤ 1)
    (fun R hR => abs_card_latticeDisc_sub_area_le hR c) hann

/-- Both branches of DH23 `basiccount0pre` (1), conditionally on a circle
exponent `e`. The elementary branch is fully proved and has its source form. -/
theorem card_annulus_disc_le_min_of_circle_error (s : Finset (Fin 2 → ℤ))
    (c d : EuclideanSpace ℝ (Fin 2)) {Q rho L C e : ℝ}
    (hQ : 2 ≤ Q) (hrho : 0 < rho) (hrhoQ : rho ≤ Q/4) (hscale : 1 ≤ Q*rho)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hdisc : ∀ R : ℝ, 1 ≤ R →
      |((latticeDisc c R).card:ℝ)-Real.pi*R^2| ≤ C*R^e)
    (hann : ∀ n ∈ s, |‖WaveTurbulence.latticePoint 1 n-c‖-Q| ≤ rho)
    (hball : ∀ n ∈ s, ‖WaveTurbulence.latticePoint 1 n-d‖ ≤ L) :
    (s.card:ℝ) ≤ min ((6*Real.pi)*(Q*rho)+(3*C)*Q^e)
      (640000*(Real.sqrt (Q*rho)+L*(Q*rho)^((3:ℝ)/2)/Q+
        L*Real.sqrt (Q*rho)*Q^(-((1:ℝ)/3)))) := by
  apply le_min
  · exact card_annulus_le_of_circle_error s c hQ hrho hrhoQ hC he0 he1 hdisc hann
  · exact card_annulus_disc_le_expanded s c d (by linarith only [hQ]) hrho.le
      (by linarith only [hQ,hrhoQ]) hscale hL hann hball

end WaveTurbulence.Counting
