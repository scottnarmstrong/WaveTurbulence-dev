/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.EventChangeBounds
public import WaveTurbulence.Foundations.Probability.CumulantMomentBounds
/-! Quantitative S7: the square-root event loss survives the whole cumulant expansion. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

/-- The number of error-bearing block selections has only exponential growth. -/
theorem card_error_selections_le {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) : (P.parts.powerset.erase ∅).card ≤ 2 ^ s.card := by
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    ((Finset.card_powerset _).le.trans (Nat.pow_le_pow_right (by decide) P.card_parts_le_card))

end WaveTurbulence.Induct
