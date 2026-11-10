/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftDescendants
/-! Lower-garden embeddings preserve and reflect descendants, and different blocks are separated. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem blockPathRoots_eq_of_base_eq {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (S : TTree → Finset TTree.Path) (z z' : Σ B : P.parts, ForestPath (low B).tree S)
    (h : ((blockPathEquiv top P low S).symm z).1 = ((blockPathEquiv top P low S).symm z').1) :
    (⟨z.1, z.2.1.1⟩ : Σ B : P.parts, Fin B.1.card) = ⟨z'.1, z'.2.1.1⟩ := by
  have h1 := blockPathEquiv_symm_base top P low S z
  have h2 := blockPathEquiv_symm_base top P low S z'
  exact (blockRootEquiv top P).symm.injective (h1.symm.trans (h.trans h2))

theorem garden_lower_block_eq_of_isDesc {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B C : P.parts) (a : GNode (low B).tree) (b : GNode (low C).tree)
    (h : (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).IsDesc
      (gardenNodeEquiv top P low (.inr ⟨C, b⟩))) : B = C := by
  have hd := (graft_attached_isDesc_iff top (blockGraftTrees top P low)
    ((blockNodeEquiv top P low).symm ⟨B, a⟩) ((blockNodeEquiv top P low).symm ⟨C, b⟩)).mp h
  exact congrArg Sigma.fst (blockPathRoots_eq_of_base_eq top P low TTree.nodes ⟨B, a⟩ ⟨C, b⟩ hd.1)

theorem garden_lower_isDesc_iff {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a b : GNode (low B).tree) :
    (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).IsDesc
      (gardenNodeEquiv top P low (.inr ⟨B, b⟩)) ↔ a.IsDesc b := by
  have ha := blockPathEquiv_symm_path top P low TTree.nodes ⟨B, a⟩
  have hb := blockPathEquiv_symm_path top P low TTree.nodes ⟨B, b⟩
  constructor
  · intro h
    have hd := (graft_attached_isDesc_iff top (blockGraftTrees top P low)
      ((blockNodeEquiv top P low).symm ⟨B, a⟩) ((blockNodeEquiv top P low).symm ⟨B, b⟩)).mp h
    have hr := blockPathRoots_eq_of_base_eq top P low TTree.nodes ⟨B, a⟩ ⟨B, b⟩ hd.1
    exact ⟨eq_of_heq (Sigma.mk.inj hr).2, ha ▸ hb ▸ hd.2⟩
  · intro h
    have hba := blockPathEquiv_symm_base top P low TTree.nodes ⟨B, a⟩
    have hbb := blockPathEquiv_symm_base top P low TTree.nodes ⟨B, b⟩
    have hroot := congrArg (fun k : Fin B.1.card => (blockRootEquiv top P).symm ⟨B, k⟩) h.1
    apply (graft_attached_isDesc_iff top (blockGraftTrees top P low)
      ((blockNodeEquiv top P low).symm ⟨B, a⟩) ((blockNodeEquiv top P low).symm ⟨B, b⟩)).mpr
    exact ⟨hba.trans (hroot.trans hbb.symm), ha.symm ▸ hb.symm ▸ h.2⟩

end WaveTurbulence.Induct
