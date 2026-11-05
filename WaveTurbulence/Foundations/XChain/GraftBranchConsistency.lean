/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopNodeEmbedding
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! Cubic momentum equations split exactly across the top and attached forests. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem branchEquation_transport {v w : ℕ} {S : Fin v → TTree} {T : Fin w → TTree}
    {V : Type*} [AddCommGroup V] (κ : GNode T → V) (e : GNode S → GNode T)
    (a : GBranch S) (b : GBranch T) (hn : b.toNode = e a.toNode)
    (hc : ∀ i, b.child i = e (a.child i)) :
    (κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)) ↔
      (κ (e a.toNode) = κ (e (a.child 0)) - κ (e (a.child 1)) + κ (e (a.child 2))) := by
  rw [hn, hc 0, hc 1, hc 2]

theorem isBranchConsistent_graft_iff {V : Type*} [AddCommGroup V] {w : ℕ}
    (top : Fin w → TTree) (P : Finpartition (univ : Finset (GLeaf top)))
    (low : (B : P.parts) → Garden B.1.card)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → V) :
    IsBranchConsistent κ ↔
      IsBranchConsistent (fun a => κ (topNodeEmbedding top P low a)) ∧
      ∀ B, IsBranchConsistent (fun a => κ (lowerNodeEmbedding top P low B a)) := by
  have ht (a : GBranch top) := branchEquation_transport κ (topNodeEmbedding top P low)
    a (gardenBranchEquiv top P low (.inl a))
    ((gardenBranch_toNode_top top P low a).trans (topNodeEmbedding_branch top P low a).symm)
    (topBranch_child top P low a)
  have hl (B : P.parts) (a : GBranch (low B).tree) :=
    branchEquation_transport κ (lowerNodeEmbedding top P low B) a
      (gardenBranchEquiv top P low (.inr ⟨B, a⟩))
      (gardenBranch_toNode_lower top P low B a) (gardenBranch_child_lower top P low B a)
  constructor
  · intro h
    exact ⟨fun a => (ht a).mp (h _), fun B a => (hl B a).mp (h _)⟩
  · rintro ⟨htop, hlow⟩ b
    obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P low).surjective b
    rcases z with a | ⟨B, a⟩
    · exact (ht a).mpr (htop a)
    · exact (hl B a).mpr (hlow B a)

end WaveTurbulence.Induct
