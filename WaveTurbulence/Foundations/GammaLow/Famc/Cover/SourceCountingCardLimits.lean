/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceGapTable
/-! Elementary cardinal bounds for the actual source counting data. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceCountingCardLimits` (sha256 f18ef05a7c289554856fe4c9942ce8a2b1f985cf371b2e95eac5072c9acead50) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

 theorem numCriticalSG_le_order {w d : ℕ} (G : Garden w) (C : CountingChoices γv G d) :
    C.numCriticalSG ≤ G.order := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (by simp only [card_univ, card_gbranch]; rfl)

 theorem hinges_card_le_order {w : ℕ} (G : Garden w) (hinges : Finset (GBranch G.tree)) :
    hinges.card ≤ G.order := by
  exact (Finset.card_le_univ hinges).trans_eq (by rw [card_gbranch]; rfl)

 theorem source_numLadders_le_rho {w : ℕ} (G : Garden w) :
    G.molecule.maximalLadders.card ≤ G.molecule.rho := by
  change G.molecule.numLadders ≤ G.molecule.numLadders + G.molecule.numFree
  omega

 theorem source_scale_count_le_rho_add_critical {w d : ℕ} (G : Garden w)
    (C : CountingChoices γv G d) :
    G.molecule.maximalLadders.card + C.numCriticalSG ≤ G.molecule.rho + C.numCriticalSG :=
  Nat.add_le_add_right (source_numLadders_le_rho G) _

end WaveTurbulence.GammaLow.Famc
