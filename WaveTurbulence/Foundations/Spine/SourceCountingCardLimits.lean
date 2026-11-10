/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourceGapTable
/-! Elementary cardinal bounds for the actual source counting data. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

 theorem source_numLadders_le_rho {w : ℕ} (G : Garden w) :
    G.molecule.maximalLadders.card ≤ G.molecule.rho := by
  change G.molecule.numLadders ≤ G.molecule.numLadders + G.molecule.numFree
  omega

end WaveTurbulence.LGSpine
