/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistForestInvolution

/-! # Involutivity of the actual insertion leaf exchange -/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (F : Fin w → TTree) (h₀ h₁ : GLeaf F) (keep : Fin 3) (t : TTree)

/-- Evaluate the insertion leaf exchange on its explicit leaf pieces. -/
theorem exchangeLeafEquiv_piece (p : InsertionLeafPiece F h₀ t) :
    exchangeLeafEquiv F h₀ h₁ keep t (insertionLeafMap F h₀ t p) =
      insertionLeafMap F h₁ (switchFree keep t)
        ((Equiv.sumCongr (outsideLeafSwap F h₀ h₁) (switchLeafEquiv keep t)) p) := by
  change (insertionLeafEquiv _ _ _) ((Equiv.sumCongr _ _)
    ((insertionLeafEquiv _ _ _).symm ((insertionLeafEquiv _ _ _) p))) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- Exchange the two holes twice to restore the exact old leaf address. -/
theorem exchangeLeafEquiv_twice_val (l : GLeaf (insertLeaf F h₀ t)) :
    (exchangeLeafEquiv F h₁ h₀ keep (switchFree keep t) (exchangeLeafEquiv F h₀ h₁ keep t l)).1 = l.1 := by
  obtain ⟨p,rfl⟩ := (insertionLeafEquiv F h₀ t).surjective l
  change (exchangeLeafEquiv F h₁ h₀ keep (switchFree keep t)
    (exchangeLeafEquiv F h₀ h₁ keep t (insertionLeafMap F h₀ t p))).1 = _
  rw [exchangeLeafEquiv_piece,exchangeLeafEquiv_piece]
  cases p with
  | inl l =>
    change (Equiv.swap h₁ h₀ (Equiv.swap h₀ h₁ l.1)).1 = l.1.1
    rw [Equiv.swap_comm h₁ h₀,Equiv.swap_apply_self]
  | inr q =>
    change (h₀.1.1,h₀.1.2 ++ switchPath keep (switchPath keep q.1)) = (h₀.1.1,h₀.1.2 ++ q.1)
    rw [switchPath_involutive]

end WaveTurbulence.Twist
