/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceGapTable
/-! Elementary cardinal bounds for the actual source counting data. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

 theorem numCriticalSG_le_order {w d : ℕ} (G : Garden w) (C : SourceVine.CountingChoices G d) :
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
    (C : SourceVine.CountingChoices G d) :
    G.molecule.maximalLadders.card + C.numCriticalSG ≤ G.molecule.rho + C.numCriticalSG :=
  Nat.add_le_add_right (source_numLadders_le_rho G) _

end WaveTurbulence.LGSpine
