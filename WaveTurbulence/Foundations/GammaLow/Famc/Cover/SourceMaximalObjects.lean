/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.Spine.SourceCountingObjects
public import Mathlib.Data.Finset.Max
/-! Maximal designated SG objects cover every eligible non-omitted object. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceMaximalObjects` (sha256 55e3832f093864858c2dc93e4006e15f149451783f2c8874f634b0b694b955ed) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

theorem eligible_atoms_disjoint {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {F : Set (GBranch G.tree)} {P : Object γv G.molecule}
    (h : eligibleSecondObject γv G L γ η base κ F P) :
    Disjoint (↑P.atoms : Set (GBranch G.tree)) F := by
  rcases h.2 with ⟨Q, hPQ, _, hQF⟩ | ⟨D, hPD, hDF⟩
  · exact disjointF_of_subset hPQ hQF
  · exact disjointF_of_subset hPD hDF

end WaveTurbulence.GammaLow.Famc
