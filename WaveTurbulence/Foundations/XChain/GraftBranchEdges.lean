/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftBranchConsistency
/-! Exact branching-edge transport and exclusion of upward edges from attached components. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem branch_isChildOf_iff {w : ℕ} {tree : Fin w → TTree} (a b : GBranch tree) :
    a.IsChildOf b ↔ ∃ i : Fin 3, a.toNode = b.child i := by
  constructor
  · rintro ⟨hr, i, hp⟩
    exact ⟨i, Subtype.ext (Prod.ext hr hp)⟩
  · rintro ⟨i, hi⟩
    have he := congrArg (fun a : GNode tree => a.1) hi
    have hr := congrArg (fun z : Fin w × TTree.Path => z.1) he
    have hp := congrArg (fun z : Fin w × TTree.Path => z.2) he
    exact ⟨hr, i, hp⟩

theorem graft_top_branch_edge_iff {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (a b : GBranch top) :
    (gardenBranchEquiv top P low (.inl a)).IsChildOf (gardenBranchEquiv top P low (.inl b)) ↔
      a.IsChildOf b := by
  have he := congrArg₂ (fun x y : Fin w × TTree.Path =>
      x.1 = y.1 ∧ ∃ i : Fin 3, x.2 = y.2 ++ [i])
    (gardenBranchEquiv_top_val top P low a) (gardenBranchEquiv_top_val top P low b)
  exact he.to_iff

theorem graft_lower_branch_edge {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a b : GBranch (low B).tree) (h : a.IsChildOf b) :
    (gardenBranchEquiv top P low (.inr ⟨B, a⟩)).IsChildOf
      (gardenBranchEquiv top P low (.inr ⟨B, b⟩)) := by
  obtain ⟨i, hi⟩ := (branch_isChildOf_iff a b).mp h
  apply (branch_isChildOf_iff _ _).mpr
  refine ⟨i, ?_⟩
  exact (gardenBranch_toNode_lower top P low B a).trans
    ((congrArg (lowerNodeEmbedding top P low B) hi).trans (gardenBranch_child_lower top P low B b i).symm)

theorem graft_child_of_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (b : GBranch (low B).tree)
    (a : GBranch (graftForest top (blockGraftTrees top P low)))
    (h : a.IsChildOf (gardenBranchEquiv top P low (.inr ⟨B, b⟩))) :
    ∃ c : GBranch (low B).tree, a = gardenBranchEquiv top P low (.inr ⟨B, c⟩) ∧ c.IsChildOf b := by
  obtain ⟨i, hi⟩ := (branch_isChildOf_iff _ _).mp h
  have hn := hi.trans (gardenBranch_child_lower top P low B b i)
  obtain ⟨z, rfl⟩ := (gardenBranchEquiv top P low).surjective a
  rcases z with a | ⟨C, a⟩
  · have he := (gardenBranch_toNode_top top P low a).symm.trans hn
    have hs := (gardenNodeEquiv top P low).injective he
    cases hs
  · have he := (gardenBranch_toNode_lower top P low C a).symm.trans hn
    have hs := Sum.inr.inj ((gardenNodeEquiv top P low).injective he)
    have hCB : C = B := congrArg Sigma.fst hs
    subst C
    have ha : a.toNode = b.child i := eq_of_heq (Sigma.mk.inj hs).2
    exact ⟨a, rfl, (branch_isChildOf_iff a b).mpr ⟨i, ha⟩⟩

end WaveTurbulence.Induct
