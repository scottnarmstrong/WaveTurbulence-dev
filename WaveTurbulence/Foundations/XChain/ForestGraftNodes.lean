/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftNodes
public import WaveTurbulence.Foundations.XChain.ForestGraft
public import WaveTurbulence.Foundations.XChain.BlockGraft
public import Mathlib.Logic.Equiv.Sum
/-! Node and branching-coordinate reindexing for a whole grafted forest. -/
@[expose] public section
namespace WaveTurbulence.Induct
open TTree

def forestNodeSigmaEquiv {w : ℕ} (tree : Fin w → TTree) :
    GNode tree ≃ Σ j : Fin w, ↥(tree j).nodes where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def forestBranchSigmaEquiv {w : ℕ} (tree : Fin w → TTree) :
    GBranch tree ≃ Σ j : Fin w, ↥(tree j).branching where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def forestAttachedPathEquiv {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (S : TTree → Finset TTree.Path) :
    (Σ j : Fin w, Σ a : ↥(top j).leaves, ↥(S (f j a.1))) ≃
      (Σ a : GLeaf top, ↥(S (f a.1.1 a.1.2))) :=
  (Equiv.sigmaAssoc (fun (j : Fin w) (a : ↥(top j).leaves) => ↥(S (f j a.1)))).symm.trans
    (Equiv.sigmaCongr (forestLeafSigmaEquiv top).symm (fun _ => Equiv.refl _))

abbrev ForestAttachedNode {w : ℕ} (top : Fin w → TTree) (f : Fin w → TTree.Path → TTree) :=
  Σ a : GLeaf top, ↥(f a.1.1 a.1.2).nodes
abbrev ForestAttachedBranch {w : ℕ} (top : Fin w → TTree) (f : Fin w → TTree.Path → TTree) :=
  Σ a : GLeaf top, ↥(f a.1.1 a.1.2).branching

noncomputable def graftForestNodeEquiv {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) :
    GBranch top ⊕ ForestAttachedNode top f ≃ GNode (graftForest top f) :=
  ((forestNodeSigmaEquiv (graftForest top f)).trans
    ((Equiv.sigmaCongrRight (fun j => (graftNodeEquiv (top j) (f j)).symm)).trans
      ((Equiv.sigmaSumDistrib (fun j => ↥(top j).branching) (fun j => AttachedNode (top j) (f j))).trans
        (Equiv.sumCongr (forestBranchSigmaEquiv top).symm
          (forestAttachedPathEquiv top f TTree.nodes))))).symm

noncomputable def graftForestBranchEquiv {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) :
    GBranch top ⊕ ForestAttachedBranch top f ≃ GBranch (graftForest top f) :=
  ((forestBranchSigmaEquiv (graftForest top f)).trans
    ((Equiv.sigmaCongrRight (fun j => (graftBranchEquiv (top j) (f j)).symm)).trans
      ((Equiv.sigmaSumDistrib (fun j => ↥(top j).branching) (fun j => AttachedBranch (top j) (f j))).trans
        (Equiv.sumCongr (forestBranchSigmaEquiv top).symm
          (forestAttachedPathEquiv top f TTree.branching))))).symm

theorem graftForestNodeEquiv_top {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (b : GBranch top) :
    (graftForestNodeEquiv top f (.inl b)).1 = b.1 := by
  rcases b with ⟨⟨j, b⟩, hb⟩
  rfl

theorem graftForestNodeEquiv_lower {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (x : ForestAttachedNode top f) :
    (graftForestNodeEquiv top f (.inr x)).1 = (x.1.1.1, x.1.1.2 ++ x.2.1) := by
  rcases x with ⟨⟨⟨j, a⟩, ha⟩, ⟨b, hb⟩⟩
  rfl

theorem graftForestBranchEquiv_top {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (b : GBranch top) :
    (graftForestBranchEquiv top f (.inl b)).1 = b.1 := by
  rcases b with ⟨⟨j, b⟩, hb⟩
  rfl

theorem graftForestBranchEquiv_lower {w : ℕ} (top : Fin w → TTree)
    (f : Fin w → TTree.Path → TTree) (x : ForestAttachedBranch top f) :
    (graftForestBranchEquiv top f (.inr x)).1 = (x.1.1.1, x.1.1.2 ++ x.2.1) := by
  rcases x with ⟨⟨⟨j, a⟩, ha⟩, ⟨b, hb⟩⟩
  rfl

end WaveTurbulence.Induct
