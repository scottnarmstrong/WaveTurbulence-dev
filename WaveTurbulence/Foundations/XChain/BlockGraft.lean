/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftedGarden
public import WaveTurbulence.Foundations.XChain.GraftBranchEquiv
/-! Canonical enumeration of partition blocks and their root trees for garden grafting. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

/-- The source forest leaf carrier as a dependent sum over its roots. -/
def forestLeafSigmaEquiv {w : ℕ} (tree : Fin w → TTree) :
    GLeaf tree ≃ Σ j : Fin w, ↥(tree j).leaves where
  toFun a := ⟨a.1.1, ⟨a.1.2, a.2⟩⟩
  invFun a := ⟨(a.1, a.2.1), a.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed finite-set enumeration assigns each top leaf its unique block and root index. -/
noncomputable def blockRootEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) :
    GLeaf top ≃ Σ B : P.parts, Fin B.1.card :=
  (show GLeaf top ≃ ↥(univ : Finset (GLeaf top)) from
    ⟨fun a => ⟨a, mem_univ _⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩).trans
    (P.equivSigmaParts.trans (Equiv.sigmaCongrRight (fun B => B.1.equivFin)))

/-- The root subtree attached to each leaf is taken from that leaf's own lower garden.
Values at non-leaf addresses are irrelevant to graftTree. -/
noncomputable def blockGraftTrees {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (j : Fin w) (a : TTree.Path) : TTree :=
  if h : a ∈ (top j).leaves then
    let z := blockRootEquiv top P ⟨(j, a), h⟩
    (low z.1).tree z.2
  else TTree.leaf

theorem blockGraftTrees_at_leaf {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (a : GLeaf top) : blockGraftTrees top P low a.1.1 a.1.2 =
      (low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2 := by
  rcases a with ⟨⟨j, a⟩, ha⟩
  simp only [blockGraftTrees, dite_eq_left ha]

end WaveTurbulence.Induct
