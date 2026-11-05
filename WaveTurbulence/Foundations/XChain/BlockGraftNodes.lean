/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.BlockGraftPairing
public import WaveTurbulence.Foundations.XChain.ForestGraftNodes
/-! Nodes and branches of the lower block gardens, with the same deterministic root enumeration. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

abbrev ForestPath {w : ℕ} (tree : Fin w → TTree) (S : TTree → Finset TTree.Path) :=
  {a : Fin w × TTree.Path // a.2 ∈ S (tree a.1)}

def forestPathSigmaEquiv {w : ℕ} (tree : Fin w → TTree) (S : TTree → Finset TTree.Path) :
    ForestPath tree S ≃ Σ j : Fin w, ↥(S (tree j)) where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def blockPathFiberEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (S : TTree → Finset TTree.Path) (a : GLeaf top) :
    ↥(S (blockGraftTrees top P low a.1.1 a.1.2)) ≃
      ↥(S ((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2)) where
  toFun b := ⟨b.1, by rw [← blockGraftTrees_at_leaf top P low a]; exact b.2⟩
  invFun b := ⟨b.1, by rw [blockGraftTrees_at_leaf top P low a]; exact b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def blockPathEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (S : TTree → Finset TTree.Path) :
    (Σ a : GLeaf top, ↥(S (blockGraftTrees top P low a.1.1 a.1.2))) ≃
      Σ B : P.parts, ForestPath (low B).tree S :=
  (Equiv.sigmaCongr (blockRootEquiv top P) (blockPathFiberEquiv top P low S)).trans
    ((Equiv.sigmaAssoc (fun (B : P.parts) (k : Fin B.1.card) => ↥(S ((low B).tree k)))).trans
      (Equiv.sigmaCongrRight (fun B => (forestPathSigmaEquiv (low B).tree S).symm)))

theorem blockPathEquiv_symm_base {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (S : TTree → Finset TTree.Path) (z : Σ B : P.parts, ForestPath (low B).tree S) :
    ((blockPathEquiv top P low S).symm z).1 = (blockRootEquiv top P).symm ⟨z.1, z.2.1.1⟩ := by
  have he : blockRootEquiv top P ((blockPathEquiv top P low S).symm z).1 = ⟨z.1, z.2.1.1⟩ :=
    congrArg (fun y : Σ B : P.parts, ForestPath (low B).tree S => (⟨y.1, y.2.1.1⟩ : Σ B : P.parts, Fin B.1.card))
      ((blockPathEquiv top P low S).apply_symm_apply z)
  have h := congrArg (blockRootEquiv top P).symm he
  simpa only [Equiv.symm_apply_apply] using h

theorem blockPathEquiv_symm_path {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (S : TTree → Finset TTree.Path) (z : Σ B : P.parts, ForestPath (low B).tree S) :
    ((blockPathEquiv top P low S).symm z).2.1 = z.2.1.2 :=
  congrArg (fun y : Σ B : P.parts, ForestPath (low B).tree S => y.2.1.2)
    ((blockPathEquiv top P low S).apply_symm_apply z)

noncomputable abbrev blockNodeEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    ForestAttachedNode top (blockGraftTrees top P low) ≃ Σ B : P.parts, GNode (low B).tree :=
  blockPathEquiv top P low TTree.nodes

noncomputable abbrev blockBranchEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    ForestAttachedBranch top (blockGraftTrees top P low) ≃ Σ B : P.parts, GBranch (low B).tree :=
  blockPathEquiv top P low TTree.branching

/-- All nodes of the grafted forest, reindexed by top branching nodes and lower garden nodes. -/
noncomputable def gardenNodeEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    GBranch top ⊕ (Σ B : P.parts, GNode (low B).tree) ≃
      GNode (graftForest top (blockGraftTrees top P low)) :=
  (Equiv.sumCongr (Equiv.refl _) (blockNodeEquiv top P low).symm).trans
    (graftForestNodeEquiv top (blockGraftTrees top P low))

/-- The time coordinates, reindexed by top branching nodes and lower garden branching nodes. -/
noncomputable def gardenBranchEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    GBranch top ⊕ (Σ B : P.parts, GBranch (low B).tree) ≃
      GBranch (graftForest top (blockGraftTrees top P low)) :=
  (Equiv.sumCongr (Equiv.refl _) (blockBranchEquiv top P low).symm).trans
    (graftForestBranchEquiv top (blockGraftTrees top P low))

end WaveTurbulence.Induct
