/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestSinglePaths
public import WaveTurbulence.Foundations.XChain.FiniteTimeCurry
public import WaveTurbulence.Foundations.XChain.GraftOrderedTimes
/-! Top-forest time coordinates and their ordered domains split exactly by root. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

noncomputable def forestRootTimeSplit {w : ℕ} (top : Fin w → TTree) :
    (GBranch top → ℝ) ≃ᵐ ((j : Fin w) → GBranch (single (top j)) → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : GBranch top => ℝ)
    (forestSingleBranchEquiv top).symm).symm.trans (finiteTimeCurry (fun j => GBranch (single (top j))))

theorem forestRootTimeSplit_apply {w : ℕ} (top : Fin w → TTree) (τ : GBranch top → ℝ)
    (j : Fin w) (b : GBranch (single (top j))) :
    forestRootTimeSplit top τ j b = τ (singleBranchToForest top j b) := rfl

theorem measurePreserving_forestRootTimeSplit {w : ℕ} (top : Fin w → TTree) :
    MeasurePreserving (forestRootTimeSplit top) volume volume :=
  ((measurePreserving_piCongrLeft (fun _ : GBranch top => (volume : Measure ℝ))
    (forestSingleBranchEquiv top).symm).symm).trans
      (measurePreserving_finiteTimeCurry (fun j => GBranch (single (top j))))

theorem forestTimeDomain_iff_roots {w : ℕ} (top : Fin w → TTree) (p t : ℝ) (τ : GBranch top → ℝ) :
    τ ∈ ForestTimeDomain top p t ↔
      ∀ j, (fun b => τ (singleBranchToForest top j b)) ∈ treeTimeDomain (top j) p t := by
  constructor
  · intro h j b
    have hb := h (singleBranchToForest top j b)
    exact ⟨hb.1, hb.2.1, fun b' hc => hb.2.2 (singleBranchToForest top j b') ⟨rfl, hc.2⟩⟩
  · intro h b
    let c : GBranch (single (top b.1.1)) := ⟨(0, b.1.2), b.2⟩
    have hb := h b.1.1 c
    refine ⟨hb.1, hb.2.1, ?_⟩
    intro b' hc
    have hm : b'.1.2 ∈ (top b.1.1).branching :=
      (congrArg (fun j => b'.1.2 ∈ (top j).branching) hc.1).mp b'.2
    let c' : GBranch (single (top b.1.1)) := ⟨(0, b'.1.2), hm⟩
    have ht := hb.2.2 c' ⟨rfl, hc.2⟩
    have he : singleBranchToForest top b.1.1 c' = b' := Subtype.ext (Prod.ext hc.1.symm rfl)
    exact (congrArg (fun v : GBranch top => τ v < τ b) he).mp ht

theorem integral_forestRootTime_prod {w : ℕ} (top : Fin w → TTree)
    (f : (j : Fin w) → (GBranch (single (top j)) → ℝ) → ℂ) :
    (∫ τ : GBranch top → ℝ, ∏ j, f j (fun b => τ (singleBranchToForest top j b))) =
      ∏ j, ∫ τ, f j τ := by
  have he : (fun τ : GBranch top → ℝ => ∏ j, f j (fun b => τ (singleBranchToForest top j b))) =
      fun τ => ∏ j, f j (forestRootTimeSplit top τ j) := by
    funext τ
    exact prod_congr rfl (fun j _ => congrArg (f j)
      (funext (fun b => (forestRootTimeSplit_apply top τ j b).symm)))
  rw [he]
  exact ((measurePreserving_forestRootTimeSplit top).integral_comp' (fun z => ∏ j, f j (z j))).trans
    (integral_fintype_prod_volume_eq_prod f)

end WaveTurbulence.Induct
