/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ExtractedCriterion
public import WaveTurbulence.Foundations.XChain.ExtractedRootLeaves
/-! CANON's relative inductive classes are realized by actual canonical lower gardens. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset

theorem extracted_isCanonG_of_canonInd {w : ℕ} (LG : LayeredGarden w)
    (U : Finset (GNode LG.garden.tree)) (hU : Canon.Rel.Antichain LG U)
    (hcp : LG.garden.CompletelyPaired (LG.leavesBelowSet U)) (p : ℕ) (h : LG.CanonInd p U) :
    IsCanonG p (extractedLayeredGarden LG U hU hcp) := by
  cases p with
  | zero => exact False.elim h
  | succ q =>
    obtain ⟨hw, _, _, hirr, V, P, hTD⟩ := Canon.Rel.canonInd_succ.mp h
    have hc := Canon.Rel.relCrit_of_topDecomp q U false V P hU hTD
    exact ⟨hw, extractedLayeredGarden_isPlain LG U hU hcp,
      extracted_irreducible_of_irreducibleAt LG U hU hcp hirr,
      extracted_criterion_of_relCrit LG U hU hcp q hc⟩

end WaveTurbulence.Induct
