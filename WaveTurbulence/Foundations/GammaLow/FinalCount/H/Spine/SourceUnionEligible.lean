/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceUnionEligible`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Eligibility of the union of two selected ordinary objects meeting at one joint, when one of
them lies in an ordinary LG/ZG container; and the union is never an omitted atom set. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_vc_hasGapKind_iff (O : Src.Object Src.γL M) (h : ∃ h, O.shape = .vc h) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind) :
    O.HasGapKind L γ η w κ k ↔
      ∃ r, M.IsBlockGap L w κ O.atoms O.upper r ∧ Molecule.gapKind L γ η r = k := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact Iff.rfl
  | hyper R => cases hs

theorem object_vc_block (O : Src.Object Src.γL M) (h : ∃ h, O.shape = .vc h) :
    M.IsBlock O.atoms O.upper O.lower := by
  obtain ⟨hh, hs⟩ := h
  rcases O with ⟨S, a, b, sh⟩
  cases sh with
  | vc h' => exact h'.1
  | hyper R => cases hs

end WaveTurbulence.GammaLow.FinalCount.H
