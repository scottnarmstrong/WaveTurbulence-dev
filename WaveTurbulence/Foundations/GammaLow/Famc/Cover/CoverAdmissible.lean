/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverTags
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomScaleExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCountingChoiceScales
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSecondCollectionExists
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceFullPairTable
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceGapTableObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceGapTableSelection
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceLadderGapExists
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOrdinaryJointPairs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsMain
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePrimaryPairChoices
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceRestrictedCarrier
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUpperJointPair
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.CoverTags
public import WaveTurbulence.Foundations.Spine.SplicedAmplitudeSupport
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
/-! Every surviving decoration of the spliced kernel is admissible for a finite tagged choice
(TARGET L2097-L2116), over arbitrary subpro choice data. -/
@[expose] public section
set_option autoImplicit false
-- Ported from main `Spine.CoverAdmissible` (sha256 2188bf7d6037b7d463d80c90f2e38e297be411819ef143f8dc04510ca7897514) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.LGSpine
open scoped Classical

variable {d : ℕ}

-- `SubproConclusions`: see `Famc.Defs.SubproConclusionsGamma`.

theorem exists_cover_choice_of_subpro_choices (hfam : FamFacts γv) {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain)
    (hM : G.molecule.IsMolecule) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (Cs : SubproChoices γv G) {L : ℝ} (hL : 2 ≤ L) (γ η : ℝ)
    (hcap : 2 * L⁻¹ ≤ L ^ (-γ + η)) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ))
    (hS : SubproConclusionsGamma γv G D Cs L γ η base roots)
    (z : GenDecoration G d roots 0) (hz : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0) :
    ∃ (t : Tag G) (s : Scales (tagChoice hfam G hM Cs L γ η base roots t) L γ η),
      (fullChoice (tagChoice hfam G hM Cs L γ η base roots t) s).Admissible L γ η base
        (bondIndex G z.1) := by
  have hL0 : L ≠ 0 := by linarith
  obtain ⟨he, hg, _⟩ := splicedMomentumAmplitude_support G D hD L γ η base z.1 hz
  have hsup := hS.support z he hg
  obtain ⟨τ, hτ⟩ : ∃ τ, sourceGapTable G L γ η base (bondIndex G z.1) = τ := ⟨_, rfl⟩
  have hK := secondOf_spec hfam G hM L γ η base Cs.forbidden τ (bondIndex G z.1) hτ
  have hK' : IsSourceSecondCollection γv G L γ η base (bondIndex G z.1) Cs.forbidden
      (secondOf hfam G hM L γ η base Cs.forbidden τ).1 (secondOf hfam G hM L γ η base Cs.forbidden τ).2 := hK
  obtain ⟨T, hT1, hT2, hT3, hT4⟩ := source_full_pair_table hfam G hp hM Cs hS.structural hL0 γ η base
    roots z _ hsup hK' (dartRank G) (dartRank_injective G)
  have hlabel : ∀ v, atomGapKind G L γ η base (bondIndex G z.1) v =
      (tagChoice hfam G hM Cs L γ η base roots (τ, T)).atomLabel v := by
    intro v
    rw [tagChoice_atomLabel hfam]
    have h1 : sourceGapTable G L γ η base (bondIndex G z.1) =
        sourceGapTable G L γ η base (kappaOf G L γ η base τ) :=
      hτ.trans (kappaOf_table G L γ η base τ (bondIndex G z.1) hτ).symm
    exact sourceGapTable_atomGapKind_eq G L γ η base (bondIndex G z.1) _ h1 v
  obtain ⟨as, ls, hadm⟩ := exists_admissible_scales_of_pair_choices G
    (tagChoice hfam G hM Cs L γ η base roots (τ, T)) hL γ η hcap base (bondIndex G z.1)
    hsup ⟨dartRank G, dartRank_injective G, _, hK', rfl⟩ hlabel
    (by intro v hv; exact hT1 v ((hlabel v).trans hv))
    hT2 hT3 hT4
  obtain ⟨s, hs⟩ := exists_scales_of_admissible _ base (bondIndex G z.1) as ls hadm
  exact ⟨(τ, T), s, hs⟩

end WaveTurbulence.GammaLow.Famc
