/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperVertexConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondClosed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.VineDelObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceCanonicalDesignation`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 R6(a): pair compatibility and covering for the canonical part of the second collection. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The canonical part still covers every atom set of the collection (and keeps the hyper
shape). -/
theorem canonicalSub_covers [Fintype V] {M : Molecule V D} (rk : D → ℕ) (K : Set (Src.Object Src.γL M))
    (P : Src.Object Src.γL M) (hP : P ∈ K) :
    ∃ Q ∈ Src.canonicalSub rk K, Q.atoms = P.atoms ∧
      ((∃ R, P.shape = .hyper R) → ∃ R, Q.shape = .hyper R) := by
  classical
  by_cases hh : ∃ R, P.shape = .hyper R
  · let : Fintype (Src.Object Src.γL M) := Fintype.ofFinite _
    let S : Finset (Src.Object Src.γL M) :=
      Finset.univ.filter (fun Q => Q ∈ K ∧ Q.atoms = P.atoms ∧ ∃ R, Q.shape = .hyper R)
    have hPS : P ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP, rfl, hh⟩
    obtain ⟨Q, hQS, hmin⟩ := S.exists_min_image (fun Q => Q.hyperRank rk) ⟨P, hPS⟩
    obtain ⟨_, hQK, hQat, hQh⟩ := Finset.mem_filter.mp hQS
    refine ⟨Q, ⟨hQK, fun Q' hQ' hat _ hQ'h => ?_⟩, hQat, fun _ => hQh⟩
    exact hmin Q' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ', hat.trans hQat, hQ'h⟩)
  · refine ⟨P, ⟨hP, fun _ _ _ h => absurd h hh⟩, rfl, fun h => absurd h hh⟩

end WaveTurbulence.GammaLow.FinalCount.H
