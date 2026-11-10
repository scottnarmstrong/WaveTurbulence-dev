/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.Spine.SourceUnionNotVine
/-! Eligibility of the union of two selected ordinary objects meeting at one joint, when one of
them lies in an ordinary LG/ZG container; and the union is never an omitted atom set. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceUnionEligible` (sha256 b3878662a5b490cb5f9a36852e39d8c897f788addb1697d3976645f2653660fc) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_vc_hasGapKind_iff (O : Object γv M) (h : ∃ h, O.shape = .vc h) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) :
    O.HasGapKind L γ η w κ k ↔
      ∃ r, M.IsBlockGap L w κ O.atoms O.upper r ∧ Molecule.gapKind L γ η r = k := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact Iff.rfl
  | hyper R => cases hs

theorem object_vc_block (O : Object γv M) (h : ∃ h, O.shape = .vc h) :
    M.IsBlock O.atoms O.upper O.lower := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact h'.1
  | hyper R => cases hs

end WaveTurbulence.GammaLow.Famc
