/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.FrequencyGuardCount
public import WaveTurbulence.Foundations.NumberTheory.PoissonStationaryGuards
import Mathlib.Tactic

/-!
# Poisson stationary transfer with internally selected critical points

The phase itself selects its stationary integer frequencies. Intermediate
value supplies their critical points; actual curvature bounds control all
other frequencies, including endpoint guards. No frequency partition or
oscillatory estimate is an input.
-/

public section

open MeasureTheory Set
open WaveTurbulence.NumberTheory

namespace WaveTurbulence.Counting

/-- A quantitative finite stationary dual approximation obtained directly
from actual derivative bounds, with no assumed critical-point selection. -/
theorem exists_stationary_dual_approximation_of_curvature_bounds {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) {a b : ℕ} (hab : a ≤ b) (N : ℕ) {r mu Lam M : ℝ}
    (hr : 0 < r) (hwidth : 2*r ≤ (b:ℝ)-a) (hmu : 0 < mu) (hM : 0 ≤ M)
    (hrange : ∀ x ∈ Icc (a:ℝ) b, 0 ≤ deriv f x ∧ deriv f x ≤ N)
    (hcurv : ∀ x ∈ Icc (a:ℝ) b, mu ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ Lam)
    (hthird : ∀ x ∈ Icc (a:ℝ) b, |iteratedDeriv 3 f x| ≤ M) :
    let S := (Finset.Icc 0 (N:ℤ)).filter (fun (nu : ℤ) =>
      deriv f ((a:ℝ)+r) ≤ (nu:ℝ) ∧ (nu:ℝ) ≤ deriv f ((b:ℝ)-r))
    ∃ c : ℤ → ℝ,
      (∀ nu ∈ S, c nu ∈ Icc ((a:ℝ)+r) ((b:ℝ)-r) ∧ deriv f (c nu) = nu) ∧
      ‖(∑ n ∈ Finset.Ico a b, expPhase (f ((n:ℝ)+1)))-
        ∑ nu ∈ S, expPhase (f (c nu)-(nu:ℝ)*c nu+1/8) /
          (Real.sqrt (deriv (deriv f) (c nu)) : ℂ)‖ ≤
        ((2*(1+Real.log N)+4*Real.log ((N:ℝ)+1))/(2*Real.pi)+1)+
        (4*Lam*r+2)*(4/Real.sqrt mu)+((N:ℝ)+1)/(Real.pi*(Lam*r))+
        ((N:ℝ)+1)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) := by
  classical
  dsimp only
  let T : Finset ℤ := Finset.Icc 0 (N:ℤ)
  let S := T.filter (fun (nu : ℤ) => deriv f ((a:ℝ)+r) ≤ (nu:ℝ) ∧ (nu:ℝ) ≤ deriv f ((b:ℝ)-r))
  let G := (T \ S).filter (fun (nu : ℤ) => |(nu:ℝ)-deriv f a| ≤ Lam*r ∨ |(nu:ℝ)-deriv f b| ≤ Lam*r)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
  have hLam : 0 < Lam := hmu.trans_le ((hcurv a ⟨le_rfl,habR⟩).1.trans (hcurv a ⟨le_rfl,habR⟩).2)
  have hS : S ⊆ T := Finset.filter_subset _ _
  have hex (nu : ℤ) : ∃ c : ℝ, nu ∈ S → c ∈ Icc ((a:ℝ)+r) ((b:ℝ)-r) ∧ deriv f c = nu := by
    by_cases hnu : nu ∈ S
    · have hfreq := (Finset.mem_filter.mp hnu).2
      obtain ⟨c,hc,he⟩ := exists_interior_critical_point_of_frequency_bounds hf2 hr hwidth hfreq
      exact ⟨c,fun _ => ⟨hc,he⟩⟩
    · exact ⟨a,fun hh => False.elim (hnu hh)⟩
  choose c hc using hex
  have hcI (nu : ℤ) (hnu : nu ∈ S) : c nu ∈ Icc (a:ℝ) b := by
    have hh := (hc nu hnu).1
    constructor <;> linarith only [hh.1,hh.2,hr]
  have hG : G ⊆ T := fun nu hnu => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hnu).1).1
  have hdisj : Disjoint S G := by
    apply Finset.disjoint_left.mpr
    intro nu hs hg
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hg).1).2 hs
  have hfar (nu : ℤ) (hnu : nu ∈ (T \ S) \ G) :
      (∀ x ∈ Icc (a:ℝ) b, deriv f x ≤ (nu:ℝ)-Lam*r) ∨
      (∀ x ∈ Icc (a:ℝ) b, (nu:ℝ)+Lam*r ≤ deriv f x) := by
    obtain ⟨hnuTS,hnuG⟩ := Finset.mem_sdiff.mp hnu
    obtain ⟨hnuT,hnuS⟩ := Finset.mem_sdiff.mp hnuTS
    have hout : ¬ (deriv f ((a:ℝ)+r) ≤ (nu:ℝ) ∧ (nu:ℝ) ≤ deriv f ((b:ℝ)-r)) :=
      fun hh => hnuS (Finset.mem_filter.mpr ⟨hnuT,hh⟩)
    have hguards : ¬ (|(nu:ℝ)-deriv f a| ≤ Lam*r ∨ |(nu:ℝ)-deriv f b| ≤ Lam*r) :=
      fun hh => hnuG (Finset.mem_filter.mpr ⟨hnuTS,hh⟩)
    exact frequency_outside_stationary_and_guards_separated hf2 hr hwidth
      (fun x hx => ⟨hmu.le.trans (hcurv x hx).1,(hcurv x hx).2⟩) hout
      (lt_of_not_ge (fun hh => hguards (Or.inl hh)))
      (lt_of_not_ge (fun hh => hguards (Or.inr hh)))
  have hbound := norm_sum_sub_stationary_dual_le_with_guards hf hab N S G c (fun _ => r)
    hmu hM (mul_pos hLam hr) hrange (fun x hx => (hcurv x hx).1) hS hG hdisj
    (fun _ _ => hr) (fun nu hnu => by have hh := (hc nu hnu).1.1; linarith only [hh])
    (fun nu hnu => by have hh := (hc nu hnu).1.2; linarith only [hh])
    (fun nu hnu => (hc nu hnu).2)
    (fun nu hnu x hx => hthird x (by
      have hh := (hc nu hnu).1
      constructor <;> linarith only [hx.1,hx.2,hh.1,hh.2])) hfar
  have hGcard : (G.card:ℝ) ≤ 4*Lam*r+2 := by
    have hh := card_frequency_guards_le (T \ S) (deriv f a) (deriv f b) (mul_pos hLam hr).le
    simpa only [G,mul_assoc] using hh
  have hTcard : (T.card:ℝ) = (N:ℝ)+1 := by
    simp [T,Int.card_Icc]
  have hScard : (S.card:ℝ) ≤ (N:ℝ)+1 := by
    rw [← hTcard]
    exact_mod_cast Finset.card_le_card hS
  have hFcard : (((T \ S) \ G).card:ℝ) ≤ (N:ℝ)+1 := by
    rw [← hTcard]
    exact_mod_cast Finset.card_le_card ((Finset.sdiff_subset : (T \ S) \ G ⊆ T \ S).trans Finset.sdiff_subset)
  have hstation : (∑ nu ∈ S, (2*Real.pi/3*M*r^4+
      2/(Real.pi*(deriv (deriv f) (c nu)*r))+2/(Real.pi*(mu*r)))) ≤
      ((N:ℝ)+1)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) := by
    calc
      _ ≤ ∑ _nu ∈ S, (2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) := by
        apply Finset.sum_le_sum
        intro nu hnu
        have htail := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
          (by positivity : 0 < Real.pi*(mu*r))
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hcurv (c nu) (hcI nu hnu)).1 hr.le) Real.pi_pos.le)
        calc
          _ ≤ 2*Real.pi/3*M*r^4+(2/(Real.pi*(mu*r))+2/(Real.pi*(mu*r))) := by linarith only [htail]
          _ = _ := by ring
      _ = (S.card:ℝ)*(2*Real.pi/3*M*r^4+4/(Real.pi*(mu*r))) := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hScard (by positivity)
  refine ⟨c,hc,?_⟩
  exact hbound.trans (add_le_add
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hGcard (by positivity)))
      (div_le_div_of_nonneg_right hFcard (by positivity))) hstation)

end WaveTurbulence.Counting
