/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.CoreTwistForest

/-! # Signs on the concrete insertion leaf pieces -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (F : Fin w → TTree) (sig : Fin w → ℤˣ)

/-- An outside leaf keeps its address and sign under insertion. -/
theorem insertionLeafMap_sign_out (h : GLeaf F) (t : TTree) (l : {l : GLeaf F // l ≠ h}) :
    nodeSign sig (insertionLeafMap F h t (.inl l)).1 = nodeSign sig l.1.1 := rfl

/-- An inserted leaf sign factors through the root insertion sign. -/
theorem insertionLeafMap_sign_in (h : GLeaf F) (t : TTree) (q : ↥t.leaves) :
    nodeSign sig (insertionLeafMap F h t (.inr q)).1 = pathSign (nodeSign sig h.1) q.1 := by
  change pathSign (sig h.1.1) (h.1.2 ++ q.1) = _
  exact pathSign_append _ _ _

/-- The outside leaf exchanged with the lower crown flips sign; all other outside leaves retain it. -/
theorem outsideLeafSwap_sign (h₀ h₁ : GLeaf F) (hs : nodeSign sig h₁.1 = -nodeSign sig h₀.1)
    (l : {l : GLeaf F // l ≠ h₀}) :
    nodeSign sig (outsideLeafSwap F h₀ h₁ l).1.1 =
      if l.1 = h₁ then -nodeSign sig l.1.1 else nodeSign sig l.1.1 := by
  by_cases he : l.1 = h₁
  · have hv : (outsideLeafSwap F h₀ h₁ l).1 = h₀ := by
      change Equiv.swap h₀ h₁ l.1 = h₀
      rw [he,Equiv.swap_apply_right]
    rw [hv,he,if_pos rfl,hs,neg_neg]
  · have hv : (outsideLeafSwap F h₀ h₁ l).1 = l.1 := by
      change Equiv.swap h₀ h₁ l.1 = l.1
      exact Equiv.swap_apply_of_ne_of_ne l.2 he
    rw [hv,if_neg he]

/-- Sign transport on the inserted leaf piece, including the single retained leaf exception. -/
theorem insertedLeafSwitch_sign (h₀ h₁ : GLeaf F)
    (hs : nodeSign sig h₁.1 = -nodeSign sig h₀.1) {t : TTree} {keep : Fin 3}
    (hkeep : keep ≠ 1) (hroot : [] ∉ t.leaves) (hk : Comb.subtree t [keep] = some .leaf)
    (q : ↥t.leaves) :
    nodeSign sig (insertionLeafMap F h₁ (switchFree keep t) (.inr (switchLeafEquiv keep t q))).1 =
      if q.1 = [keep] then -nodeSign sig (insertionLeafMap F h₀ t (.inr q)).1
      else nodeSign sig (insertionLeafMap F h₀ t (.inr q)).1 := by
  rw [insertionLeafMap_sign_in,insertionLeafMap_sign_in,hs]
  exact switched_leaf_sign hkeep hroot hk _ q.2

end WaveTurbulence.Twist
