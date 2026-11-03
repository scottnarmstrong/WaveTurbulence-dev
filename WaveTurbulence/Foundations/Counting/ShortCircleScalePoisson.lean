/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.CurvaturePoissonTransfer
public import WaveTurbulence.Foundations.NumberTheory.CircleTotalPoissonErrorScale
import Mathlib.Tactic

/-!
# Short source windows at the circle scales

If the source window is shorter than twice the balanced radius, endpoint
guards cover its stationary range. Uniform curvature estimates and the
separated-frequency test then bound the original sum directly.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.Counting

/-- Short windows need no dual-sum estimate: their entire actual sum is
bounded by the quantitative circle error scale. -/
theorem norm_sum_le_circle_scale_of_short_window {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {a b : ℕ} (hab : a ≤ b) (N : ℕ) {w U : ℝ}
    (hw : 1 ≤ w) (hU : 1 ≤ U) (hUw : U ≤ w^2) (hwU : w ≤ U^2)
    (hwidth : (b:ℝ)-a ≤ 2*stationaryBalancingRadius w U)
    (hrange : ∀ x ∈ Icc (a:ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hN : (N:ℝ)+1 ≤ 3*(w*U^(-((1:ℝ)/2))))
    (hcurv : ∀ x ∈ Icc (a:ℝ) b,
      w*U^(-((3:ℝ)/2))/8 ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ w*U^(-((3:ℝ)/2))) :
    ‖∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1))‖ ≤
      2320*(w^((11:ℝ)/30)*U^((7:ℝ)/20)) := by
  classical
  let r := stationaryBalancingRadius w U
  let mu : ℝ := w*U^(-((3:ℝ)/2))/8
  let Lam : ℝ := w*U^(-((3:ℝ)/2))
  let T : Finset ℤ := Finset.Icc 0 (N:ℤ)
  let G := T.filter (fun (nu : ℤ) => |(nu:ℝ)-deriv f a| ≤ Lam*r ∨ |(nu:ℝ)-deriv f b| ≤ Lam*r)
  have hwp : 0 < w := zero_lt_one.trans_le hw
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hmu : 0 < mu := by dsimp only [mu]; positivity
  have hLam : 0 < Lam := by dsimp only [Lam]; positivity
  have hr : 0 < r := stationaryBalancingRadius_pos hwp hUp
  have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfar (nu : ℤ) (hnu : nu ∈ (T \ (∅ : Finset ℤ)) \ G) :
      (∀ x ∈ Icc (a:ℝ) b, deriv f x ≤ (nu:ℝ)-Lam*r) ∨
      (∀ x ∈ Icc (a:ℝ) b, (nu:ℝ)+Lam*r ≤ deriv f x) := by
    simp only [Finset.sdiff_empty,Finset.mem_sdiff] at hnu
    have hguards : ¬ (|(nu:ℝ)-deriv f a| ≤ Lam*r ∨ |(nu:ℝ)-deriv f b| ≤ Lam*r) :=
      fun hh => hnu.2 (Finset.mem_filter.mpr ⟨hnu.1,hh⟩)
    exact frequency_outside_guards_separated_of_short_interval hf2 habR hLam.le hwidth
      (fun x hx => ⟨hmu.le.trans (hcurv x hx).1,(hcurv x hx).2⟩)
      (lt_of_not_ge (fun hh => hguards (Or.inl hh)))
      (lt_of_not_ge (fun hh => hguards (Or.inr hh)))
  have hbound := norm_sum_sub_stationary_dual_le_with_guards hf hab N ∅ G
    (fun _ => 0) (fun _ => 1) hmu (M := 0) (by norm_num) (mul_pos hLam hr) hrange
    (fun x hx => (hcurv x hx).1) (Finset.empty_subset _) (Finset.filter_subset _ _)
    (Finset.disjoint_empty_left _)
    (by simp) (by simp) (by simp) (by simp) (by simp) hfar
  simp only [Finset.sum_empty,sub_zero,Finset.sdiff_empty,add_zero] at hbound
  have hGcard : (G.card:ℝ) ≤ 4*Lam*r+2 := by
    have hh := card_frequency_guards_le T (deriv f a) (deriv f b) (mul_pos hLam hr).le
    simpa only [G,mul_assoc] using hh
  have hTcard : (T.card:ℝ) = (N:ℝ)+1 := by simp [T,Int.card_Icc]
  have hFcard : ((T \ G).card:ℝ) ≤ (N:ℝ)+1 := by
    rw [← hTcard]
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : T \ G ⊆ T)
  have hcost := circle_scale_total_poisson_error_le hw hU hUw hwU N hN
  have hstation : 0 ≤ ((N:ℝ)+1)*(2*Real.pi/3*(3*w*U^(-((5:ℝ)/2)))*r^4+4/(Real.pi*(mu*r))) := by positivity
  have hpartial := hbound.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hGcard (by positivity)))
    (div_le_div_of_nonneg_right hFcard (by positivity)))
  exact hpartial.trans (by
    change ((2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1)+
      (4*Lam*r+2)*(4/Real.sqrt mu)+((N:ℝ)+1)/(Real.pi*(Lam*r)) ≤ _
    linarith only [hcost,hstation])

end WaveTurbulence.Counting
