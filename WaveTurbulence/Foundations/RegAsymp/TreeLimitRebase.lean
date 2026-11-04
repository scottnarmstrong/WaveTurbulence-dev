/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Cancel.RegType2
public import WaveTurbulence.Foundations.ClassJR.MCTShift

/-! # Exact rebasing of the limiting tree chain

The continuation's vanishing below the lone-leaf time allows the same change
of lower endpoint as for the original oscillatory chain, without an extra
integrability assumption or a new approximate-identity theorem.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set Cancel ClassJR

/-- The limiting chain cannot sample a continuation above its upper endpoint. -/
theorem tree_chainL_eq_zero_of_le (D : ℕ → ℝ → ℂ) :
    ∀ (c : LegalCode) (q : ℕ) {s : ℝ}, 0 ≤ s → ∀ {g : ℝ → ℂ},
      (∀ u ≤ s, g u = 0) → ∀ {t : ℝ}, t ≤ s → chainL D c q t g = 0
  | .nil, _, _, _, _, hg, _, ht => hg _ ht
  | .node .nil r, q, s, hs, g, hg, t, ht => by
    simp only [chainL]
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℂ)) (fun u hu => ?_)]
    · simp
    have hu' : u ≤ s := (Set.mem_uIcc.mp hu).elim (fun h => h.2.trans ht) (fun h => h.2.trans hs)
    rw [tree_chainL_eq_zero_of_le D r _ hs hg hu', mul_zero]
  | .node (.node _ _) _, _, _, _, _, _, _, _ => rfl

/-- Exact rebase of the actual limiting chain for a continuation vanishing below s. -/
theorem tree_chainL_rebase (D : ℕ → ℝ → ℂ) :
    ∀ (c : LegalCode) (q : ℕ) {s : ℝ}, 0 ≤ s → ∀ {g : ℝ → ℂ},
      (∀ u ≤ s, g u = 0) → ∀ {t : ℝ}, s ≤ t →
        chainL D c q t g = chainL (fun j u => D j (u+s)) c q (t-s) (fun u => g (u+s))
  | .nil, _, _, _, _, _, _, _ => by simp only [chainL, sub_add_cancel]
  | .node .nil r, q, s, hs, g, hg, t, hst => by
    simp only [chainL]
    let F := fun u => D q u * chainL D r (q+1) u g
    have hzero : ∀ u ∈ uIcc 0 s, F u = 0 := by
      intro u hu
      have hu' : u ≤ s := (Set.mem_uIcc.mp hu).elim (fun h => h.2) (fun h => h.2.trans hs)
      dsimp only [F]
      rw [tree_chainL_eq_zero_of_le D r _ hs hg hu', mul_zero]
    have he : (∫ u in s..t, F u) = ∫ u in (0:ℝ)..(t-s), F (u+s) := by
      rw [intervalIntegral.integral_comp_add_right F s, zero_add, sub_add_cancel]
    change (∫ u in (0:ℝ)..t, F u) = _
    rw [← intervalIntegral_eq_of_eq_zero hzero t, he]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (sub_nonneg.mpr hst)] at hu
    dsimp only [F]
    rw [tree_chainL_rebase D r _ hs hg (show s ≤ u+s by linarith [hu.1]), add_sub_cancel_right]
  | .node (.node _ _) _, _, _, _, _, _, _, _ => rfl

/-- At a positive endpoint a limiting chain only samples positive continuation times. -/
theorem tree_chainL_congr_pos (D : ℕ → ℝ → ℂ) :
    ∀ (c : LegalCode) (q : ℕ) {g g' : ℝ → ℂ}, (∀ u, 0 < u → g u = g' u) →
      ∀ {t : ℝ}, 0 < t → chainL D c q t g = chainL D c q t g'
  | .nil, _, _, _, hg, _, ht => hg _ ht
  | .node .nil r, q, g, g', hg, t, ht => by
    simp only [chainL]
    apply intervalIntegral.integral_congr_ae
    exact Filter.Eventually.of_forall (fun u hu => by
      rw [uIoc_of_le ht.le] at hu
      rw [tree_chainL_congr_pos D r _ hg hu.1])
  | .node (.node _ _) _, _, _, _, _, _, _ => rfl

end WaveTurbulence.RegAsymp
