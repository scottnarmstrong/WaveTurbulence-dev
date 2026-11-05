/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestRootPhaseProducts
/-! The actual forest phase integral is the product of its signed single-tree phase integrals. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI

theorem forest_phaseIndicator_eq_roots {w d : ℕ} (L γ δ : ℝ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (κ : GNode top → (Fin d → ℤ)) (p t : ℝ) (τ : GBranch top → ℝ) :
    (ForestTimeDomain top p t).indicator
      (forestPhaseProd L γ δ sig top (fun a => latticePoint L (κ a))) τ =
    ∏ j, zpowSign (sig j) ((treeTimeDomain (top j) p t).indicator
      (phaseFn L γ δ (top j) (fun a => κ (singleNodeToForest top j a)))
      (fun b => τ (singleBranchToForest top j b))) := by
  classical
  by_cases h : ∀ j, (fun b => τ (singleBranchToForest top j b)) ∈ treeTimeDomain (top j) p t
  · rw [Set.indicator_of_mem ((forestTimeDomain_iff_roots top p t τ).mpr h)]
    have he := prod_congr (s₁ := (univ : Finset (Fin w))) rfl (fun j _ =>
      congrArg (zpowSign (sig j)) (Set.indicator_of_mem (h j)
        (phaseFn L γ δ (top j) (fun a => κ (singleNodeToForest top j a)))))
    exact (forestPhaseProd_eq_roots L γ δ top sig κ τ).trans he.symm
  · have hn : τ ∉ ForestTimeDomain top p t := fun he => h ((forestTimeDomain_iff_roots top p t τ).mp he)
    rw [Set.indicator_of_notMem hn]
    obtain ⟨j, hj⟩ := Classical.not_forall.mp h
    symm
    apply prod_eq_zero (mem_univ j)
    rw [Set.indicator_of_notMem hj]
    simp only [zpowSign, map_zero, ite_self]

theorem forestPhaseIntegral_eq_roots {w d : ℕ} (L γ δ : ℝ) (top : Fin w → TTree)
    (sig : Fin w → ℤˣ) (κ : GNode top → (Fin d → ℤ)) (p t : ℝ) :
    forestPhaseIntegral L γ δ sig top (fun a => latticePoint L (κ a)) p t =
      ∏ j, zpowSign (sig j) (timeInt L γ δ (top j) (fun a => κ (singleNodeToForest top j a)) p t) := by
  have he := integral_congr_ae (μ := (volume : Measure (GBranch top → ℝ)))
    (ae_of_all _ (fun τ => forest_phaseIndicator_eq_roots L γ δ top sig κ p t τ))
  have hi := integral_forestRootTime_prod top (fun j τ => zpowSign (sig j)
    ((treeTimeDomain (top j) p t).indicator
      (phaseFn L γ δ (top j) (fun a => κ (singleNodeToForest top j a))) τ))
  have hz := prod_congr (s₁ := (univ : Finset (Fin w))) rfl (fun j _ =>
    (zpowSign_integral volume (sig j) ((treeTimeDomain (top j) p t).indicator
      (phaseFn L γ δ (top j) (fun a => κ (singleNodeToForest top j a))))).symm)
  exact he.trans (hi.trans hz)

end WaveTurbulence.Induct
