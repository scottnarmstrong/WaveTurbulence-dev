/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.InsertionLeafPieces

/-! # The actual leaf exchange underlying a unit twist

TARGET twist: swap the lower subtree and the leaf paired with u23,
interchanging the two free child subtrees. The map is an actual bijection
between the leaf sets of the two concrete ordered forests.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- Actual leaf bijection induced by the free-child switch. -/
@[expose] def switchLeafEquiv (keep : Fin 3) (t : TTree) : ↥t.leaves ≃ ↥(switchFree keep t).leaves where
  toFun q := ⟨switchPath keep q.1,(switchPath_leaf_iff keep t q.1).mpr q.2⟩
  invFun q := ⟨switchPath keep q.1,by
    apply (switchPath_leaf_iff keep t (switchPath keep q.1)).mp
    simpa only [switchPath_involutive keep q.1] using q.2⟩
  left_inv q := Subtype.ext (switchPath_involutive keep q.1)
  right_inv q := Subtype.ext (switchPath_involutive keep q.1)

/-- Actual branch bijection induced by the free-child switch. -/
@[expose] def switchBranchEquiv (keep : Fin 3) (t : TTree) :
    ↥t.branching ≃ ↥(switchFree keep t).branching where
  toFun q := ⟨switchPath keep q.1,(switchPath_branch_iff keep t q.1).mpr q.2⟩
  invFun q := ⟨switchPath keep q.1,by
    apply (switchPath_branch_iff keep t (switchPath keep q.1)).mp
    simpa only [switchPath_involutive keep q.1] using q.2⟩
  left_inv q := Subtype.ext (switchPath_involutive keep q.1)
  right_inv q := Subtype.ext (switchPath_involutive keep q.1)

/-- Swap the two hole leaves on the outside carrier, fixing every other leaf. -/
@[expose] def outsideLeafSwap {w : ℕ} (F : Fin w → TTree) (h₀ h₁ : GLeaf F) :
    {l : GLeaf F // l ≠ h₀} ≃ {l : GLeaf F // l ≠ h₁} where
  toFun l := ⟨Equiv.swap h₀ h₁ l.1,by
    intro he
    exact l.2 ((Equiv.swap h₀ h₁).injective (he.trans (Equiv.swap_apply_left h₀ h₁).symm))⟩
  invFun l := ⟨Equiv.swap h₀ h₁ l.1,by
    intro he
    exact l.2 ((Equiv.swap h₀ h₁).injective (he.trans (Equiv.swap_apply_right h₀ h₁).symm))⟩
  left_inv l := Subtype.ext (Equiv.swap_apply_self h₀ h₁ l.1)
  right_inv l := Subtype.ext (Equiv.swap_apply_self h₀ h₁ l.1)

/-- The concrete leaf bijection for moving the lower crown from h0 to h1. -/
@[expose] noncomputable def exchangeLeafEquiv {w : ℕ} (F : Fin w → TTree)
    (h₀ h₁ : GLeaf F) (keep : Fin 3) (t : TTree) :
    GLeaf (insertLeaf F h₀ t) ≃ GLeaf (insertLeaf F h₁ (switchFree keep t)) :=
  (insertionLeafEquiv F h₀ t).symm.trans
    ((Equiv.sumCongr (outsideLeafSwap F h₀ h₁) (switchLeafEquiv keep t)).trans
      (insertionLeafEquiv F h₁ (switchFree keep t)))

end WaveTurbulence.Twist
