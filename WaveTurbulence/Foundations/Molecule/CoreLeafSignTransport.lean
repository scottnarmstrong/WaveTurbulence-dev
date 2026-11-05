/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreLeafPieces

/-! # Leaf-sign compatibility of the concrete unit twist

TARGET twistexplain: the exchanged leaf pair flips signs and all other
leaves retain theirs. This discharges the actual garden constructor.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Evaluate the actual leaf exchange on a decomposed old leaf. -/
theorem coreLeafEquiv_piece (p : InsertionLeafPiece (commonForest G P.lower)
    (collapsedRoot G P.lower) (lowerCrown G P.lower)) :
    coreLeafEquiv G P ((coreLeafPiece G P).symm p) =
      insertionLeafMap (commonForest G P.lower) (pairedHole G P) (switchFree P.keep (lowerCrown G P.lower))
        ((Equiv.sumCongr (outsideLeafSwap (commonForest G P.lower) (collapsedRoot G P.lower) (pairedHole G P))
          (switchLeafEquiv P.keep (lowerCrown G P.lower))) p) := by
  change (insertionLeafEquiv _ _ _) ((Equiv.sumCongr _ _)
    ((insertionLeafEquiv _ _ _).symm ((forestLeafCast (restore_commonForest G P.lower).symm)
      ((forestLeafCast (restore_commonForest G P.lower).symm).symm ((insertionLeafEquiv _ _ _) p))))) = _
  simp only [Equiv.apply_symm_apply,Equiv.symm_apply_apply]
  rfl

/-- Exact sign compatibility, with no sign-transport premise. -/
theorem coreLeafEquiv_sign (l : GLeaf G.tree) :
    nodeSign G.sig (coreLeafEquiv G P l).1 = coreLeafMultiplier G P l * G.sign l.toNode := by
  classical
  obtain ⟨p,rfl⟩ := (coreLeafPiece G P).symm.surjective l
  rw [coreLeafEquiv_piece]
  have holes : nodeSign G.sig (pairedHole G P).1 = -nodeSign G.sig (collapsedRoot G P.lower).1 :=
    CorePlacement.hole_signs G P
  cases p with
  | inl k =>
    have hret : (coreLeafPiece G P).symm (.inl k) ≠ P.retained := by
      intro he
      have hh := congrArg (coreLeafPiece G P) he
      rw [Equiv.apply_symm_apply,coreLeafPiece_retained] at hh
      cases hh
    have hpair : (coreLeafPiece G P).symm (.inl k) = G.pair P.retained ↔ k.1 = pairedHole G P := by
      rw [Equiv.symm_apply_eq,coreLeafPiece_paired,Sum.inl.injEq]
      exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
    change nodeSign G.sig (insertionLeafMap _ _ _ (.inl (outsideLeafSwap _ _ _ k))).1 = _
    rw [insertionLeafMap_sign_out]
    have hs := outsideLeafSwap_sign (commonForest G P.lower) G.sig
      (collapsedRoot G P.lower) (pairedHole G P) holes k
    rw [hs]
    simp only [coreLeafMultiplier,hret,hpair,false_or]
    change (if k.1 = pairedHole G P then -nodeSign G.sig k.1.1 else nodeSign G.sig k.1.1) =
      (if k.1 = pairedHole G P then -1 else 1) * nodeSign G.sig k.1.1
    split <;> simp
  | inr q =>
    have hret : (coreLeafPiece G P).symm (.inr q) = P.retained ↔ q.1 = [P.keep] := by
      rw [Equiv.symm_apply_eq,coreLeafPiece_retained,Sum.inr.injEq]
      exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
    have hpair : (coreLeafPiece G P).symm (.inr q) ≠ G.pair P.retained := by
      intro he
      have hh := congrArg (coreLeafPiece G P) he
      rw [Equiv.apply_symm_apply,coreLeafPiece_paired] at hh
      cases hh
    change nodeSign G.sig (insertionLeafMap _ _ _ (.inr (switchLeafEquiv _ _ q))).1 = _
    have hs := insertedLeafSwitch_sign (commonForest G P.lower) G.sig
      (collapsedRoot G P.lower) (pairedHole G P) holes P.outer
      (lowerCrown_root_not_leaf G P) (lowerCrown_retained_leaf G P) q
    rw [hs]
    simp only [coreLeafMultiplier,hret,hpair,or_false]
    change (if q.1 = [P.keep] then -nodeSign G.sig (insertionLeafMap _ _ _ (.inr q)).1
      else nodeSign G.sig (insertionLeafMap _ _ _ (.inr q)).1) =
      (if q.1 = [P.keep] then -1 else 1) * nodeSign G.sig (insertionLeafMap _ _ _ (.inr q)).1
    split <;> simp

end WaveTurbulence.Twist
