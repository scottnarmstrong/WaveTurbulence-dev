/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.VineEst.BlockGraft
/-! The exact equivalence between grafted lower leaves and the disjoint lower gardens. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

noncomputable def blockLeafFiberEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (a : GLeaf top) :
    ↥(blockGraftTrees top P low a.1.1 a.1.2).leaves ≃
      ↥((low (blockRootEquiv top P a).1).tree (blockRootEquiv top P a).2).leaves where
  toFun b := ⟨b.1, by rw [← blockGraftTrees_at_leaf top P low a]; exact b.2⟩
  invFun b := ⟨b.1, by rw [blockGraftTrees_at_leaf top P low a]; exact b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every lower leaf lies in exactly one block garden, and its root and path are preserved. -/
noncomputable def blockLeafEquiv {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card) :
    AttachedLeaf top (blockGraftTrees top P low) ≃ Σ B : P.parts, GLeaf (low B).tree :=
  (Equiv.sigmaCongr (blockRootEquiv top P) (blockLeafFiberEquiv top P low)).trans
    ((Equiv.sigmaAssoc (fun (B : P.parts) (k : Fin B.1.card) => ↥((low B).tree k).leaves)).trans
      (Equiv.sigmaCongrRight (fun B => (forestLeafSigmaEquiv (low B).tree).symm)))

theorem blockLeafEquiv_block {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : AttachedLeaf top (blockGraftTrees top P low)) :
    (blockLeafEquiv top P low x).1 = (blockRootEquiv top P x.1).1 := rfl

theorem blockLeafEquiv_root {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : AttachedLeaf top (blockGraftTrees top P low)) :
    (blockLeafEquiv top P low x).2.1.1 = (blockRootEquiv top P x.1).2 := rfl

theorem blockLeafEquiv_path {w : ℕ} (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (x : AttachedLeaf top (blockGraftTrees top P low)) :
    (blockLeafEquiv top P low x).2.1.2 = x.2.1 := rfl

/-- The root-sign constraint gives equality of inherited and lower-garden signs. -/
theorem blockLeafEquiv_sign {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (x : AttachedLeaf top (blockGraftTrees top P low)) :
    nodeSign (low (blockLeafEquiv top P low x).1).sig (blockLeafEquiv top P low x).2.1 =
      attachedSign sig x := by
  change TTree.pathSign ((low (blockRootEquiv top P x.1).1).sig (blockRootEquiv top P x.1).2) x.2.1 = _
  rw [hsig]
  have he : (blockRootEquiv top P).symm ⟨(blockRootEquiv top P x.1).1,
      (blockRootEquiv top P x.1).2⟩ = x.1 := (blockRootEquiv top P).symm_apply_apply x.1
  rw [he]

end WaveTurbulence.LGSpine
