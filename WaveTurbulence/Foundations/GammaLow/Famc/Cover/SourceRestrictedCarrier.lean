/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperBlockFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourcePairsCompatible
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceCountingData
public import WaveTurbulence.Foundations.Spine.SourcePairsCompatible
/-! R6(b): the restricted carrier of the second collection, compared with the conclusion of
TARGET subpro(4) as recorded in `SubproSupport.contained`.

TARGET L2101–L2112: the candidates of `C_2` are the SG vine-like objects of `M_sb` covered by
subpro(4): SG, not contained in an object of `C_1`, disjoint from the hinges, and contained in a DV
or in an LG/ZG vine-like object, where the DV / container is disjoint from the hinges and from
every object of `C_1`. `eligibleSecondObject γv G L γ η base κ F` with `F = C.forbidden` is exactly
that predicate (the explicit conditions "outside `C_1`" and "disjoint from the hinges" follow from
the container conditions because an object has a joint in its atom set). -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceRestrictedCarrier` (sha256 2c156a657d658355c692e9345462039211074d4c862121c9c0c4f0e9b4f26aaf) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {w d : ℕ}

/-- The candidate predicate read literally off `SubproSupport.contained` (L2040–L2051, subpro(4))
and L2101–L2104. -/
@[expose] def literalSecondCandidate {G : Garden w} (C : SubproChoices γv G) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (P : Object γv G.molecule) : Prop :=
  P.HasGapKind L γ η base κ .SG ∧ C.OutsideAtoms P ∧ Disjoint P.atoms C.hinges ∧
    ((∃ S a b, IsDV γv G.molecule S a b ∧ P.atoms ⊆ S ∧
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms) ∨
    ∃ Q : Object γv G.molecule, P.atoms ⊆ Q.atoms ∧
      (Q.HasGapKind L γ η base κ .LG ∨ Q.HasGapKind L γ η base κ .ZG) ∧
      Disjoint Q.atoms C.hinges ∧ ∀ i, Disjoint Q.atoms (C.collection i).atoms)

theorem disjoint_forbidden_iff {G : Garden w} (C : SubproChoices γv G) (S : Finset (GBranch G.tree)) :
    Disjoint (↑S : Set (GBranch G.tree)) C.forbidden ↔
      Disjoint S C.hinges ∧ ∀ i, Disjoint S (C.collection i).atoms := by
  unfold SubproChoices.forbidden
  rw [Set.disjoint_union_right, Set.disjoint_iUnion_right]
  simp only [Finset.disjoint_coe]

/-- Every eligible object (designation-level containment `Object.IsContained`) satisfies the atom-set
candidate predicate (R28 (3)). -/
theorem eligibleSecondObject_to_literal {G : Garden w} (C : SubproChoices γv G) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (P : Object γv G.molecule)
    (h : eligibleSecondObject γv G L γ η base κ C.forbidden P) :
    literalSecondCandidate C L γ η base κ P := by
  have hne : P.upper ∈ P.atoms := object_mem_of_joint P (Or.inl rfl)
  obtain ⟨hsg, h | ⟨D, hPD, hDF⟩⟩ := h
  · obtain ⟨Q, hPQ, hk, hQF⟩ := h
    obtain ⟨hQ1, hQ2⟩ := (disjoint_forbidden_iff C _).mp hQF
    have hPsub := hPQ
    refine ⟨hsg, fun i hPi => ?_, Finset.disjoint_of_subset_left hPsub hQ1,
      Or.inr ⟨Q, hPsub, hk, hQ1, hQ2⟩⟩
    exact Finset.disjoint_left.mp (hQ2 i) (hPsub hne) (hPi hne)
  · obtain ⟨h1, h2⟩ := (disjoint_forbidden_iff C _).mp hDF
    refine ⟨hsg, fun i hPi => ?_, Finset.disjoint_of_subset_left hPD h1,
      Or.inl ⟨D.first ∪ D.second, D.upper, D.lower,
        ⟨D.sigma_one, D.first, D.second, D.first_vine, D.second_vine, D.overlap, rfl⟩, hPD, h1, h2⟩⟩
    exact Finset.disjoint_left.mp (h2 i) (hPD hne) (hPi hne)

/-- AMEND5 (R42(2)): with atom-level `eligibleSecondObject` the converse holds, so the second-collection
eligibility IS the literal candidate predicate of subpro(4) (and `source_literal_object_classification`
classifies every eligible object). -/
theorem literal_to_eligibleSecondObject {G : Garden w} (C : SubproChoices γv G) (L γ η : ℝ)
    (base : Mom d) (κ : GardenDart G → (Fin d → ℤ)) (P : Object γv G.molecule)
    (h : literalSecondCandidate C L γ η base κ P) :
    eligibleSecondObject γv G L γ η base κ C.forbidden P := by
  obtain ⟨hsg, _, _, h | ⟨Q, hPQ, hk, hQ1, hQ2⟩⟩ := h
  · obtain ⟨S, a, b, ⟨hσ, f, s, hf, hs, hov, rfl⟩, hPS, hS1, hS2⟩ := h
    exact ⟨hsg, Or.inr ⟨⟨f, s, a, b, hσ, hf, hs, hov⟩, hPS,
      (disjoint_forbidden_iff C _).mpr ⟨hS1, hS2⟩⟩⟩
  · exact ⟨hsg, Or.inl ⟨Q, hPQ, hk, (disjoint_forbidden_iff C _).mpr ⟨hQ1, hQ2⟩⟩⟩

/-- TARGET L2116, second half (`C_2` side): no hinge atom lies in any object of the (canonical,
restricted) second collection, in particular no hinge is interior to one. This is derived from the
restricted carrier, not assumed. -/
theorem hinge_not_in_second {G : Garden w} (C : CountingChoices γv G d) (L γ η : ℝ) (base : Mom d)
    (κ : GardenDart G → (Fin d → ℤ)) (h : C.SecondCollectionOK L γ η base κ) :
    ∀ v ∈ C.subpro.hinges, ∀ P ∈ C.secondCollection, v ∉ P.atoms := by
  obtain ⟨rk, _, K, hK, hC⟩ := h
  intro v hv P hP hvP
  rw [hC] at hP
  have hdis := eligible_atoms_disjoint ((hK.2.2 P).mp hP.1).1
  exact Set.disjoint_left.mp hdis (Finset.mem_coe.mpr hvP) (Or.inl (Finset.mem_coe.mpr hv))

theorem hingeOutsideSecond_of_secondCollectionOK {G : Garden w} (C : CountingChoices γv G d)
    (L γ η : ℝ) (base : Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (h : C.SecondCollectionOK L γ η base κ) :
    ∀ v ∈ C.subpro.hinges, ∀ P ∈ C.secondCollection, ¬ P.IsInterior v :=
  fun v hv P hP hi => hinge_not_in_second C L γ η base κ h v hv P hP hi.1

end WaveTurbulence.GammaLow.Famc
