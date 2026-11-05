/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBranchEdges
public import WaveTurbulence.Foundations.XChain.GraftTimeSplit
public import WaveTurbulence.Foundations.XChain.MarkedLayeredGraft
/-! Separation of time ordering across a graft, independently of marks and kernel weights. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

def ForestTimeDomain {w : ℕ} (top : Fin w → TTree) (p t : ℝ) :
    Set (GBranch top → ℝ) :=
  {τ | ∀ b, p < τ b ∧ τ b < t ∧ ∀ b', b'.IsChildOf b → τ b' < τ b}

def BranchOrdered {w : ℕ} (tree : Fin w → TTree) (τ : GBranch tree → ℝ) : Prop :=
  ∀ a b, a.IsChildOf b → τ a < τ b

theorem branchOrdered_graft_iff {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (τ : GBranch (graftForest top (blockGraftTrees top P low)) → ℝ) (p : ℝ)
    (htop : ∀ b, p < (graftTimeSplit top P low τ).1 b)
    (hlow : ∀ B b, (graftTimeSplit top P low τ).2 ⟨B, b⟩ < p) :
    BranchOrdered (graftForest top (blockGraftTrees top P low)) τ ↔
      BranchOrdered top (graftTimeSplit top P low τ).1 ∧
      ∀ B, BranchOrdered (low B).tree (fun b => (graftTimeSplit top P low τ).2 ⟨B, b⟩) := by
  constructor
  · intro h
    refine ⟨fun a b hab => h _ _ ((graft_top_branch_edge_iff top P low a b).mpr hab), ?_⟩
    intro B a b hab
    exact h _ _ (graft_lower_branch_edge top P low B a b hab)
  · rintro ⟨ht, hl⟩ a b hab
    obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P low).surjective b
    rcases z with b | ⟨B, b⟩
    · obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P low).surjective a
      rcases z with a | ⟨B, a⟩
      · exact ht a b ((graft_top_branch_edge_iff top P low a b).mp hab)
      · exact (hlow B a).trans (htop b)
    · obtain ⟨c, rfl, hc⟩ := graft_child_of_lower top P low B b a hab
      exact hl B c b hc

end WaveTurbulence.Induct
