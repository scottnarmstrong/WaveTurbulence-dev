/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedSubforest
/-! The literal pairing induced on a completely paired antichain subforest. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem subforestLeafMap_sign {w : ℕ} {tree : Fin w → TTree} (sig : Fin w → ℤˣ)
    (U : Finset (GNode tree)) (ℓ : GLeaf (subforestTrees U)) :
    nodeSign (fun k => nodeSign sig (subforestRoot U k).1) ℓ.1 =
      nodeSign sig (subforestLeafMap U ℓ).1 := by
  exact (pathSign_append (sig (subforestRoot U ℓ.1.1).1.1)
    (subforestRoot U ℓ.1.1).1.2 ℓ.1.2).symm

noncomputable def extractedPair {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) :
    GLeaf (subforestTrees U) → GLeaf (subforestTrees U) :=
  fun ℓ => (subforestLeafEquiv LG U hU).symm
    ⟨LG.garden.pair (subforestLeafEquiv LG U hU ℓ).1, (hcp _ (subforestLeafEquiv LG U hU ℓ).2).2⟩

theorem extractedPair_image {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (ℓ : GLeaf (subforestTrees U)) :
    (subforestLeafEquiv LG U hU (extractedPair LG U hU hcp ℓ)).1 =
      LG.garden.pair (subforestLeafEquiv LG U hU ℓ).1 := by
  have he := (subforestLeafEquiv LG U hU).apply_symm_apply
    ⟨LG.garden.pair (subforestLeafEquiv LG U hU ℓ).1, (hcp _ (subforestLeafEquiv LG U hU ℓ).2).2⟩
  exact congrArg Subtype.val he

theorem extractedPair_involutive {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) :
    Function.Involutive (extractedPair LG U hU hcp) := by
  intro ℓ
  apply (subforestLeafEquiv LG U hU).injective
  apply Subtype.ext
  exact (extractedPair_image LG U hU hcp (extractedPair LG U hU hcp ℓ)).trans
    ((congrArg LG.garden.pair (extractedPair_image LG U hU hcp ℓ)).trans (LG.garden.pair_pair _))

theorem extractedPair_ne_self {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (ℓ : GLeaf (subforestTrees U)) :
    extractedPair LG U hU hcp ℓ ≠ ℓ := by
  intro he
  have hv := congrArg (fun l => (subforestLeafEquiv LG U hU l).1) he
  exact (hcp _ (subforestLeafEquiv LG U hU ℓ).2).1
    ((extractedPair_image LG U hU hcp ℓ).symm.trans hv)

noncomputable def extractedGarden {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) : Garden U.card where
  sig := fun k => nodeSign LG.garden.sig (subforestRoot U k).1
  tree := subforestTrees U
  pair := extractedPair LG U hU hcp
  mark := fun _ => none
  pair_pair := extractedPair_involutive LG U hU hcp
  pair_eq_iff ℓ := by
    simp only [ne_eq, not_true_eq_false, iff_false]
    exact extractedPair_ne_self LG U hU hcp ℓ
  pair_sign ℓ _ := by
    have hs (l : GLeaf (subforestTrees U)) := subforestLeafMap_sign LG.garden.sig U l
    have hp := congrArg (fun l : GLeaf LG.garden.tree => nodeSign LG.garden.sig l.1)
      (extractedPair_image LG U hU hcp ℓ)
    have hsign := LG.garden.pair_sign (subforestLeafEquiv LG U hU ℓ).1
      (hcp _ (subforestLeafEquiv LG U hU ℓ).2).1
    exact (hs _).trans (hp.trans (hsign.trans (congrArg Neg.neg (hs ℓ).symm)))

end WaveTurbulence.Induct
