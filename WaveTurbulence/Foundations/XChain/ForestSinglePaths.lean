/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestGraftNodes
public import WaveTurbulence.Foundations.XChain.TopTreeLeafProducts
/-! Forest nodes and branching nodes split exactly into their single-tree root components. -/
@[expose] public section
namespace WaveTurbulence.Induct

noncomputable def singlePathEquiv (T : TTree) (S : TTree → Finset TTree.Path) :
    {a : Fin 1 × TTree.Path // a.2 ∈ S T} ≃ ↥(S T) where
  toFun a := ⟨a.1.2, a.2⟩
  invFun a := ⟨(0, a.1), a.2⟩
  left_inv _ := Subtype.ext (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

noncomputable def forestSingleBranchEquiv {w : ℕ} (top : Fin w → TTree) :
    GBranch top ≃ Σ j : Fin w, GBranch (single (top j)) :=
  (forestBranchSigmaEquiv top).trans (Equiv.sigmaCongrRight (fun j => (singlePathEquiv (top j) TTree.branching).symm))

noncomputable def singleNodeToForest {w : ℕ} (top : Fin w → TTree) (j : Fin w)
    (a : GNode (single (top j))) : GNode top := ⟨(j, a.1.2), a.2⟩

noncomputable def singleBranchToForest {w : ℕ} (top : Fin w → TTree) (j : Fin w)
    (b : GBranch (single (top j))) : GBranch top := ⟨(j, b.1.2), b.2⟩

theorem forestSingleBranchEquiv_symm_apply {w : ℕ} (top : Fin w → TTree) (j : Fin w)
    (b : GBranch (single (top j))) :
    (forestSingleBranchEquiv top).symm ⟨j, b⟩ = singleBranchToForest top j b := rfl

end WaveTurbulence.Induct
