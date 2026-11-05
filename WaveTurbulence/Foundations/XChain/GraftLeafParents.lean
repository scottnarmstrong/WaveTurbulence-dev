/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBranchEdges
public import WaveTurbulence.Foundations.XChain.GraftDecoration
/-! Marked-leaf parents are preserved within every attached lower component. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem branch_isParentOf_iff {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (ℓ : GLeaf tree) :
    b.IsParentOf ℓ ↔ ∃ i : Fin 3, ℓ.toNode = b.child i := by
  constructor
  · rintro ⟨hr, i, hp⟩
    exact ⟨i, Subtype.ext (Prod.ext hr hp)⟩
  · rintro ⟨i, hi⟩
    have he := congrArg (fun a : GNode tree => a.1) hi
    have hr := congrArg (fun z : Fin w × TTree.Path => z.1) he
    have hp := congrArg (fun z : Fin w × TTree.Path => z.2) he
    exact ⟨hr, i, hp⟩

theorem graft_lower_leaf_parent {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (b : GBranch (low B).tree) (ℓ : GLeaf (low B).tree) (h : b.IsParentOf ℓ) :
    (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).IsParentOf (lowerLeafEmbedding top P low B ℓ) := by
  obtain ⟨i, hi⟩ := (branch_isParentOf_iff b ℓ).mp h
  apply (branch_isParentOf_iff _ _).mpr
  exact ⟨i, (gardenLeaf_toNode_lower top P low B ℓ).trans
    ((congrArg (lowerNodeEmbedding top P low B) hi).trans (gardenBranch_child_lower top P low B b i).symm)⟩

theorem graft_leaf_child_of_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (b : GBranch (low B).tree)
    (ℓ : GLeaf (graftForest top (blockGraftTrees top P low)))
    (h : (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).IsParentOf ℓ) :
    ∃ l : GLeaf (low B).tree, ℓ = lowerLeafEmbedding top P low B l ∧ b.IsParentOf l := by
  obtain ⟨i, hi⟩ := (branch_isParentOf_iff _ _).mp h
  have hn := hi.trans (gardenBranch_child_lower top P low B b i)
  obtain ⟨⟨C, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
  have he := (gardenLeaf_toNode_lower top P low C l).symm.trans hn
  have hs := Sum.inr.inj ((gardenNodeEquiv top P low).injective he)
  have hCB : C = B := congrArg Sigma.fst hs
  subst C
  have hl : l.toNode = b.child i := eq_of_heq (Sigma.mk.inj hs).2
  exact ⟨l, rfl, (branch_isParentOf_iff b l).mpr ⟨i, hl⟩⟩

theorem markedGardenGraft_flowerParent_lower_iff {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (b : GBranch (low B).tree) :
    (markedGardenGraft sig top P low hsig).IsFlowerParent
      (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) ↔ (low B).IsFlowerParent b := by
  constructor
  · rintro ⟨ℓ, hflower, hparent⟩
    obtain ⟨l, rfl, hl⟩ := graft_leaf_child_of_lower top P low B b ℓ hparent
    have hm := markedGardenGraft_mark_lower sig top P low hsig B l
    exact ⟨l, hm.symm.trans hflower, hl⟩
  · rintro ⟨l, hflower, hparent⟩
    have hm := markedGardenGraft_mark_lower sig top P low hsig B l
    exact ⟨lowerLeafEmbedding top P low B l, hm.trans hflower,
      graft_lower_leaf_parent top P low B b l hparent⟩

end WaveTurbulence.Induct
