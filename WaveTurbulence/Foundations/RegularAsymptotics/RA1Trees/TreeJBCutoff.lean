/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TimeDegree
public import WaveTurbulence.Foundations.ClassJR.MCTShift

/-! # The lone-leaf indicator gives exactly the source tree lower clock -/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set ClassJR

private theorem real_intervalIntegral_eq_of_eq_zero {f : ℝ → ℝ} {s : ℝ}
    (h0 : ∀ u ∈ uIcc 0 s, f u = 0) (t : ℝ) :
    (∫ u in s..t, f u) = ∫ u in (0:ℝ)..t, f u := by
  apply Complex.ofReal_injective
  have h := intervalIntegral_eq_of_eq_zero (f := fun u => (f u:ℂ))
    (fun u hu => by rw [h0 u hu, Complex.ofReal_zero]) t
  simpa only [intervalIntegral.integral_ofReal] using h

/-- The source real chain vanishes when its continuation is zero below its upper clock. -/
theorem tree_JBchain_eq_zero_of_le : ∀ (X : RegChain) {s : ℝ}, 0 ≤ s →
    ∀ {g : ℝ → ℝ}, (∀ u ≤ s, g u = 0) → ∀ {t : ℝ}, t ≤ s →
      X.JBchain 0 0 t g = 0
  | .nil, _, _, _, hg, _, ht => hg _ ht
  | .pair _ r g _ rest, s, hs, F, hF, t, ht => by
    simp only [RegChain.JBchain]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun u hu => ?_)]
    · simp
    have hu' : u ≤ s := (Set.mem_uIcc.mp hu).elim (fun h => h.2.trans ht) (fun h => h.2.trans hs)
    rw [tree_JBchain_eq_zero_of_le rest hs hF hu', mul_zero]

/-- The original indicator continuation restricts the entire ordered tree chain to s<t.
No source time factor is replaced, and no new root clock is assumed. -/
theorem tree_JBchain_cutoff_eq : ∀ (X : RegChain) (t s : ℝ), 0 ≤ s → s < t →
    X.JBchain 0 0 t (fun u => if s < u then 1 else 0) = X.JBchain 0 s t (fun _ => 1)
  | .nil, t, s, _, hst => by simp only [RegChain.JBchain, ite_eq_left hst]
  | .pair _ r g _ rest, t, s, hs, hst => by
    let F := fun u => r.JB 0 u u * g.JB 0 u u *
      rest.JBchain 0 0 u (fun v => if s < v then 1 else 0)
    have hzero : ∀ u ∈ uIcc 0 s, F u = 0 := by
      intro u hu
      have hu' : u ≤ s := (Set.mem_uIcc.mp hu).elim (fun h => h.2) (fun h => h.2.trans hs)
      dsimp only [F]
      rw [tree_JBchain_eq_zero_of_le rest hs
        (fun v hv => by simp [not_lt.mpr hv]) hu', mul_zero]
    simp only [RegChain.JBchain]
    change (∫ u in (0:ℝ)..t, F u) = _
    rw [← real_intervalIntegral_eq_of_eq_zero hzero t]
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun u hu => by
      rw [uIoc_of_le hst.le] at hu
      dsimp only [F]
      rw [tree_JBchain_cutoff_eq rest u s hs hu.1])

theorem tree_JBchain_cutoff_eq_JBtree (X : RegChain) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    X.JBchain 0 0 t (fun u => if s < u then 1 else 0) = X.JBtree 0 t s := by
  rw [RegChain.JBtree,max_eq_left hs]
  exact tree_JBchain_cutoff_eq X t s hs hst

end WaveTurbulence.RegAsymp
