/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftPhaseIndicator
public import WaveTurbulence.Foundations.XChain.UnmarkedPhaseIntegral
public import WaveTurbulence.Foundations.XChain.GraftLowerTimeIntegrals
/-! Exact integrated phase factorization for arbitrary top trees and plain lower components. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory

theorem markedGardenGraft_isPlain {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hplain : ∀ B, (low B).IsPlain) : (markedGardenGraft sig top P low hsig).IsPlain := by
  intro ℓ
  obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
  exact (markedGardenGraft_mark_lower sig top P low hsig B l).trans (hplain B l)

end WaveTurbulence.Induct
