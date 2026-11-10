/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverAdmissible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.CoverTags
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomKindAtJoints
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceAtomScaleExists
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCanonicalDesignation
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceCountingCardLimits
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
public import WaveTurbulence.Foundations.Spine.CoverAdmissible
public import WaveTurbulence.Foundations.Spine.SourceCountingCardLimits
/-! The finite cover index, its geometry and its weight budget (TARGET L2088, L2097-L2116),
over arbitrary subpro choice data. -/
@[expose] public section
set_option autoImplicit false
-- Ported from main `Spine.CoverFinite` (sha256 98337cb80eee4136c5753f76964b4b00af1ad817fd230e0ebadd0e25f530aa96) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.LGSpine
open scoped Classical

variable {d : ℕ}

/-- The finite index of occurring counting choices of the spliced kernel. -/
def CoverIndex (hfam : FamFacts γv) {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule) (D : SplicedKernelData G d)
    (Cs : SubproChoices γv G) (L γ η : ℝ) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) :=
  {j : (t : Tag G) × Scales (tagChoice hfam G hM Cs L γ η base roots t) L γ η //
    ∃ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 ∧
      (fullChoice (tagChoice hfam G hM Cs L γ η base roots j.1) j.2).Admissible L γ η base
        (bondIndex G z.1)}

noncomputable def CoverIndex.choice (hfam : FamFacts γv) {R : ℕ} {G : Garden (2 * R)} {hM : G.molecule.IsMolecule}
    {D : SplicedKernelData G d} {Cs : SubproChoices γv G} {L γ η : ℝ} {base : Mom d}
    {roots : Fin (2 * R) → (Fin d → ℤ)} (j : CoverIndex hfam G hM D Cs L γ η base roots) :
    CountingChoices γv G d :=
  fullChoice (tagChoice hfam G hM Cs L γ η base roots j.1.1) j.1.2

theorem finite_scales {w : ℕ} {G : Garden w} (B : CountingChoices γv G d) {L : ℝ} (hL : 0 < L)
    (γ η : ℝ) (hb : L ^ (-γ + η) ≤ 1) : Finite (Scales B L γ η) := by
  have := finite_sourcePositiveLadderScale hL
  have : Finite (AtomScale L γ η) :=
    Finite.of_injective
      (fun P : AtomScale L γ η => (⟨P.1, P.2.1, P.2.2.1, P.2.2.2.trans hb⟩ : SourcePositiveLadderScale L))
      (fun P Q h => Subtype.ext (by simpa using congrArg Subtype.val h))
  unfold Scales LadderChoices
  infer_instance

theorem finite_coverIndex (hfam : FamFacts γv) {R : ℕ} (G : Garden (2 * R)) (hM : G.molecule.IsMolecule)
    (D : SplicedKernelData G d) (Cs : SubproChoices γv G) {L : ℝ} (hL : 0 < L) (γ η : ℝ)
    (hb : L ^ (-γ + η) ≤ 1) (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) :
    Finite (CoverIndex hfam G hM D Cs L γ η base roots) := by
  have : ∀ t : Tag G, Finite (Scales (tagChoice hfam G hM Cs L γ η base roots t) L γ η) :=
    fun t => finite_scales _ hL γ η hb
  have : Finite (Tag G) := inferInstance
  have : Finite ((t : Tag G) × Scales (tagChoice hfam G hM Cs L γ η base roots t) L γ η) :=
    inferInstance
  unfold CoverIndex
  infer_instance

/-- Geometry of every occurring choice: subpro (1),(2), the hinge assertions of TARGET L2116
(C1 half is a hypothesis, C2 half is derived), and the hinge SG labels. -/
theorem coverIndex_geometry_of_subpro_choices (hfam : FamFacts γv) {R : ℕ} (G : Garden (2 * R))
    (hM : G.molecule.IsMolecule) (hconn : G.molecule.IsConnected)
    (hatoms : G.molecule.atoms.card = G.order) (hbonds : G.molecule.bonds.card + R = 2 * G.order)
    (D : SplicedKernelData G d)
    (Cs : SubproChoices γv G) {L : ℝ} (γ η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) (hS : SubproConclusionsGamma γv G D Cs L γ η base roots)
    (j : CoverIndex hfam G hM D Cs L γ η base roots) :
    CountingGeometry G j.choice := by
  obtain ⟨z, hz, hadm⟩ := j.2
  have hadm' : (CoverIndex.choice hfam j).Admissible L γ η base (bondIndex G z.1) := hadm
  obtain ⟨hsub, hsec, hlab, _⟩ := hadm'
  refine ⟨hM, hconn, hatoms, hbonds, hS.structural, ?_, ?_, hS.hingeOutsideFirst, ?_,
    hS.tripleDesignated, hS.hingeNoLoop⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro v hv
    have hl : atomGapKind G L γ η base (bondIndex G z.1) v = (CoverIndex.choice hfam j).atomLabel v :=
      hlab v
    rw [← hl]
    obtain ⟨x, y, _, _, hxy⟩ := hsub.hingeSG v hv
    exact (source_atomGapKind_eq_SG_iff G L γ η base _ v).mpr ⟨x, y, hxy⟩
  · exact hingeOutsideSecond_of_secondCollectionOK _ L γ η base _ hsec

end WaveTurbulence.GammaLow.Famc
