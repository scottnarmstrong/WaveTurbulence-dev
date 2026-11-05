/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GardenDataExt
public import WaveTurbulence.Foundations.XChain.MarkedLayeredGraft
public import WaveTurbulence.Foundations.XChain.GraftPlainPhaseIntegral
/-! Ordinary grafting is the plain specialization of the generic marked construction. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem markedGardenGraft_eq_gardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hplain : ∀ B, (low B).IsPlain)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    markedGardenGraft sig top P low hsig = gardenGraft sig top P low hplain hsig := by
  apply garden_eq_of_raw_data (markedGardenGraft sig top P low hsig)
    (gardenGraft sig top P low hplain hsig) rfl rfl
  · intro a b hab
    have he : a = b := Subtype.ext hab
    subst b
    rfl
  · intro a _ _
    exact markedGardenGraft_isPlain sig top P low hsig hplain a

theorem markedLayeredGardenGraft_eq_layeredGardenGraft {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card)
    (p : ℕ) (hplain : ∀ B, (low B).garden.IsPlain)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p) :
    markedLayeredGardenGraft sig top P low p hsig hbound =
      layeredGardenGraft sig top P low p hplain hsig hbound := by
  apply layeredGarden_eq_of_raw_data
  · exact markedGardenGraft_eq_gardenGraft sig top P _ hplain hsig
  · intro a b hab
    exact congrArg (graftLayer top P low p) (Subtype.ext hab)

end WaveTurbulence.Induct
