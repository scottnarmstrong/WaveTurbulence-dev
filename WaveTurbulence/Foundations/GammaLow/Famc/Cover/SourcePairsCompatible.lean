/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
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
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceSwapObject
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionAtoms
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceOneJointPairFalse
public import WaveTurbulence.Foundations.Spine.SourceObjectPairUniqueness
public import WaveTurbulence.Foundations.Spine.SourceHyperDiamondObjects
/-! Compatibility of the joint pairs of the selected secondary objects: two members of the second
collection sharing a joint use the same dart pair there, except that two different designations
of one hyper group (the triple-bond example) may differ. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourcePairsCompatible` (sha256 78b8494520ad178d1458ca1c2736e4c8d01aa5fca085c005f82372f4f9318353) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem object_shape_cases (O : Object γv M) :
    (∃ h, O.shape = .vc h) ∨ (∃ R, O.shape = .hyper R) := by
  rcases hh : O.shape with h | R
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨R, rfl⟩

theorem containsDart_vc {O : Object γv M} (h : ∃ h, O.shape = .vc h) (x : D) :
    O.ContainsDart x ↔ M.InGroup O.atoms x := by
  obtain ⟨hh, hs⟩ := h
  unfold Object.ContainsDart
  rw [hs]

theorem object_contained_of_card_lt' (P Q : Object γv M) (hsub : P.atoms ⊆ Q.atoms)
    (hlt : P.atoms.card < Q.atoms.card) : P.IsContained Q := by
  rcases P with ⟨A, x, y, P⟩
  rcases Q with ⟨S, a, b, Q⟩
  cases P <;> cases Q
  · exact hsub
  · exact hsub
  · exact hsub
  · exact ⟨hsub, fun he => False.elim ((Nat.ne_of_lt hlt) (congrArg Finset.card he))⟩

theorem object_vc_degIn (O : Object γv M) (h : ∃ h, O.shape = .vc h) {v : V}
    (hv : v = O.upper ∨ v = O.lower) : M.degIn O.atoms v = 2 := by
  have hd := Mole.block_joint_degrees M (object_vc_block O h)
  rcases hv with rfl | rfl
  · exact hd.1
  · exact hd.2

theorem object_hyper_degIn (O : Object γv M) (h : ∃ R, O.shape = .hyper R) {v : V}
    (hv : v = O.upper ∨ v = O.lower) : M.degIn O.atoms v = 3 := by
  obtain ⟨a, _, h3, _⟩ := object_oh_at O (hv.imp Eq.symm Eq.symm)
  exact h3 h

theorem object_mem_of_joint (O : Object γv M) {v : V} (hv : v = O.upper ∨ v = O.lower) :
    v ∈ O.atoms := by
  have hb := (object_oh O).basic
  rcases hv with rfl | rfl
  · exact hb.2.1
  · exact hb.2.2.1

theorem nested_pairs {w d : ℕ} {G : Garden w} {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)}
    {F : Set (GBranch G.tree)} {omitted : Set (Finset (GBranch G.tree))} {collection : Set (Object γv G.molecule)}
    (hc : IsSourceSecondCollection γv G L γ η base κ F omitted collection)
    {P Q : Object γv G.molecule} (hPm : P ∈ collection) (hQm : Q ∈ collection)
    (hsub : P.atoms ⊆ Q.atoms) {v : GBranch G.tree} (hvP : v = P.upper ∨ v = P.lower)
    (hvQ : v = Q.upper ∨ v = Q.lower) {x y x' y' : GardenDart G}
    (hxy : SourceObjectJointPair P v x y) (hxy' : SourceObjectJointPair Q v x' y') :
    (x = x' ∧ y = y') ∨ (P.atoms = Q.atoms ∧ (∃ R, P.shape = .hyper R) ∧ ∃ R, Q.shape = .hyper R) := by
  obtain ⟨hQel, hQo, _⟩ := (hc.2.2 Q).mp hQm
  obtain ⟨_, _, hPmax⟩ := (hc.2.2 P).mp hPm
  by_cases heq : P.atoms = Q.atoms
  · rcases object_shape_cases P with hP | hP <;> rcases object_shape_cases Q with hQ | hQ
    · left
      have h1 : SourceObjectJointPair P v x' y' := by
        obtain ⟨a1, a2, g1, g2, o1, o2⟩ := hxy'
        refine ⟨a1, a2, (containsDart_vc hP _).mpr ?_, (containsDart_vc hP _).mpr ?_, o1, o2⟩
        · rw [heq]; exact (containsDart_vc hQ _).mp g1
        · rw [heq]; exact (containsDart_vc hQ _).mp g2
      exact (source_object_joint_pair_unique P hvP hxy h1)
    · exfalso
      have h1 := object_vc_degIn P hP hvP
      have h2 := object_hyper_degIn Q hQ hvQ
      rw [heq] at h1; omega
    · exfalso
      have h1 := object_hyper_degIn P hP hvP
      have h2 := object_vc_degIn Q hQ hvQ
      rw [heq] at h1; omega
    · exact Or.inr ⟨heq, hP, hQ⟩
  · exfalso
    have hlt : P.atoms.card < Q.atoms.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩)
    have h2 := hPmax Q hQel hQo (object_contained_of_card_lt' P Q hsub hlt)
    exact absurd (Finset.card_le_card (Object.contained_atoms_subset Q P h2)) (by omega)

end WaveTurbulence.GammaLow.Famc
