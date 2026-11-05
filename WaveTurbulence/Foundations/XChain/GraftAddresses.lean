/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraftNodes
/-! Address formulas for transporting graph incidences through the actual garden graft. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

noncomputable def gardenLeafEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    GLeaf (graftForest top (blockGraftTrees top P low)) ≃ Σ B : P.parts, GLeaf (low B).tree :=
  (graftForestLeafEquiv top (blockGraftTrees top P low)).symm.trans (blockLeafEquiv top P low)

theorem gardenNodeEquiv_top_val {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) : (gardenNodeEquiv top P low (.inl b)).1 = b.1 := by
  rcases b with ⟨⟨j, b⟩, hb⟩
  rfl

theorem gardenBranchEquiv_top_val {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) : (gardenBranchEquiv top P low (.inl b)).1 = b.1 := by
  rcases b with ⟨⟨j, b⟩, hb⟩
  rfl

theorem gardenNodeEquiv_lower_val {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GNode (low B).tree) :
    (gardenNodeEquiv top P low (.inr ⟨B, a⟩)).1 =
      let ℓ := (blockRootEquiv top P).symm ⟨B, a.1.1⟩
      (ℓ.1.1, ℓ.1.2 ++ a.1.2) := by
  have hb : ((blockNodeEquiv top P low).symm ⟨B, a⟩).1 =
      (blockRootEquiv top P).symm ⟨B, a.1.1⟩ := blockPathEquiv_symm_base top P low TTree.nodes ⟨B, a⟩
  have hp : ((blockNodeEquiv top P low).symm ⟨B, a⟩).2.1 = a.1.2 :=
    blockPathEquiv_symm_path top P low TTree.nodes ⟨B, a⟩
  exact (graftForestNodeEquiv_lower top (blockGraftTrees top P low)
    ((blockNodeEquiv top P low).symm ⟨B, a⟩)).trans
      (congrArg₂ (fun (ℓ : GLeaf top) (b : TTree.Path) => (ℓ.1.1, ℓ.1.2 ++ b)) hb hp)


theorem gardenBranchEquiv_lower_val {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GBranch (low B).tree) :
    (gardenBranchEquiv top P low (.inr ⟨B, a⟩)).1 =
      let ℓ := (blockRootEquiv top P).symm ⟨B, a.1.1⟩
      (ℓ.1.1, ℓ.1.2 ++ a.1.2) := by
  have hb : ((blockBranchEquiv top P low).symm ⟨B, a⟩).1 =
      (blockRootEquiv top P).symm ⟨B, a.1.1⟩ := blockPathEquiv_symm_base top P low TTree.branching ⟨B, a⟩
  have hp : ((blockBranchEquiv top P low).symm ⟨B, a⟩).2.1 = a.1.2 :=
    blockPathEquiv_symm_path top P low TTree.branching ⟨B, a⟩
  exact (graftForestBranchEquiv_lower top (blockGraftTrees top P low)
    ((blockBranchEquiv top P low).symm ⟨B, a⟩)).trans
      (congrArg₂ (fun (ℓ : GLeaf top) (b : TTree.Path) => (ℓ.1.1, ℓ.1.2 ++ b)) hb hp)


theorem gardenLeafEquiv_symm_val {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GLeaf (low B).tree) :
    ((gardenLeafEquiv top P low).symm ⟨B, a⟩).1 =
      let ℓ := (blockRootEquiv top P).symm ⟨B, a.1.1⟩
      (ℓ.1.1, ℓ.1.2 ++ a.1.2) := by
  have hb : ((blockLeafEquiv top P low).symm ⟨B, a⟩).1 =
      (blockRootEquiv top P).symm ⟨B, a.1.1⟩ := blockPathEquiv_symm_base top P low TTree.leaves ⟨B, a⟩
  have hp : ((blockLeafEquiv top P low).symm ⟨B, a⟩).2.1 = a.1.2 :=
    blockPathEquiv_symm_path top P low TTree.leaves ⟨B, a⟩
  exact congrArg₂ (fun (ℓ : GLeaf top) (b : TTree.Path) => (ℓ.1.1, ℓ.1.2 ++ b)) hb hp


theorem gardenBranch_toNode_top {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (b : GBranch top) :
    (gardenBranchEquiv top P low (.inl b)).toNode = gardenNodeEquiv top P low (.inl b) := by
  apply Subtype.ext
  exact (gardenBranchEquiv_top_val top P low b).trans (gardenNodeEquiv_top_val top P low b).symm

theorem gardenBranch_toNode_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (b : GBranch (low B).tree) :
    (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).toNode =
      gardenNodeEquiv top P low (.inr ⟨B, b.toNode⟩) := by
  apply Subtype.ext
  exact (gardenBranchEquiv_lower_val top P low B b).trans (gardenNodeEquiv_lower_val top P low B b.toNode).symm

theorem gardenLeaf_toNode_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (a : GLeaf (low B).tree) :
    ((gardenLeafEquiv top P low).symm ⟨B, a⟩).toNode =
      gardenNodeEquiv top P low (.inr ⟨B, a.toNode⟩) := by
  apply Subtype.ext
  exact (gardenLeafEquiv_symm_val top P low B a).trans (gardenNodeEquiv_lower_val top P low B a.toNode).symm

theorem gardenBranch_child_lower {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (B : P.parts) (b : GBranch (low B).tree) (i : Fin 3) :
    (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).child i =
      gardenNodeEquiv top P low (.inr ⟨B, b.child i⟩) := by
  apply Subtype.ext
  change ((gardenBranchEquiv top P low (.inr ⟨B, b⟩)).1.1,
    (gardenBranchEquiv top P low (.inr ⟨B, b⟩)).1.2 ++ [i]) = _
  rw [gardenBranchEquiv_lower_val, gardenNodeEquiv_lower_val]
  simp only [GBranch.child, List.append_assoc]

end WaveTurbulence.Induct
