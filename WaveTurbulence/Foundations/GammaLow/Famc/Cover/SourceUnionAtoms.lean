/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDVUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperAbsorb
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceHyperDiamondObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceOneJointContradiction
/-! Where the union of two selected ordinary objects meeting at one joint lies: inside the
LG/ZG container or double vine that makes the first object eligible. No hypothesis on the
shape of the union (block or hyper-block) is used. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceUnionAtoms` (sha256 2d322068093eef0ad0de8b137bac6d5a464ebd10e99994e6588413c5b1aac2b4) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

theorem one_joint_union_contained (hfam : FamFacts γv) {w d : ℕ} (G : Garden w)
    (hM : G.molecule.IsMolecule) {L γ η : ℝ} {base : Mom d}
    {κ : GardenDart G → (Fin d → ℤ)} {c0 : GBranch G.tree → Mom d}
    {F : Set (GBranch G.tree)}
    (hκ : G.molecule.IsDecoration L base c0 κ)
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c0 v = 0)
    {P Q : Object γv G.molecule} {cj : GBranch G.tree}
    (hPvc : ∃ h, P.shape = .vc h) (hQvc : ∃ h, Q.shape = .vc h)
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPQ : P.atoms ∩ Q.atoms = {cj})
    (hPsg : P.HasGapKind L γ η base κ .SG) (hQsg : Q.HasGapKind L γ η base κ .SG)
    (hQF : Disjoint (↑Q.atoms : Set (GBranch G.tree)) F)
    (hPel : (∃ C : Object γv G.molecule, P.atoms ⊆ C.atoms ∧
      (C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) ∧
      Disjoint (↑C.atoms : Set (GBranch G.tree)) F) ∨
      ∃ D : DoubleVine γv G, P.atoms ⊆ D.first ∪ D.second ∧
        Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F) :
    (∃ C : Object γv G.molecule, (C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) ∧
      P.atoms ∪ Q.atoms ⊆ C.atoms ∧ (∃ h, C.shape = .vc h) ∧
      Disjoint (↑C.atoms : Set (GBranch G.tree)) F) ∨
    (∃ C : Object γv G.molecule, (C.HasGapKind L γ η base κ .LG ∨ C.HasGapKind L γ η base κ .ZG) ∧
      P.atoms ∪ Q.atoms ⊆ C.atoms ∧ (∃ R, C.shape = .hyper R) ∧
      Disjoint (↑C.atoms : Set (GBranch G.tree)) F) ∨
    ∃ D : DoubleVine γv G, P.atoms ∪ Q.atoms ⊆ D.first ∪ D.second ∧
      Disjoint (↑(D.first ∪ D.second) : Set (GBranch G.tree)) F := by
  have hPB0 := object_vc_block P hPvc
  have hQB0 := object_vc_block Q hQvc
  have hcP : cj ∈ P.atoms := hPl ▸ hPB0.2.2.1
  have hcQ : cj ∈ Q.atoms := hQu ▸ hQB0.2.1
  rcases hPel with ⟨C, hPC, hCk, hCF⟩ | ⟨D, hPD, hDF⟩
  · have hsub : P.atoms ⊆ C.atoms := hPC
    by_cases hCvc : ∃ h, C.shape = .vc h
    · left
      refine ⟨C, hCk, ?_, hCvc, hCF⟩
      have hCB := object_vc_block C hCvc
      obtain ⟨rP, hrP, hkP⟩ := (object_vc_hasGapKind_iff P hPvc L γ η base κ .SG).mp hPsg
      obtain ⟨rQ, hrQ, hkQ⟩ := (object_vc_hasGapKind_iff Q hQvc L γ η base κ .SG).mp hQsg
      obtain ⟨rC, hrC, hkC⟩ : ∃ rC, G.molecule.IsBlockGap L base κ C.atoms C.upper rC ∧
          (Molecule.gapKind L γ η rC = .LG ∨ Molecule.gapKind L γ η rC = .ZG) := by
        rcases hCk with h | h
        · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff C hCvc L γ η base κ .LG).mp h
          exact ⟨r, hr, Or.inl hk⟩
        · obtain ⟨r, hr, hk⟩ := (object_vc_hasGapKind_iff C hCvc L γ η base κ .ZG).mp h
          exact ⟨r, hr, Or.inr hk⟩
      have habs := Vine.SG_block_outer_joints_absent G.molecule hM hCB hPB0 hsub L γ η base c0 κ
        hκ hc0 hrC hrP hkC hkP
      have hcCj : cj ≠ C.upper ∧ cj ≠ C.lower :=
        ⟨fun h => habs.1 (h ▸ hcP), fun h => habs.2 (h ▸ hcP)⟩
      have hCQ : ¬ C.atoms ⊆ Q.atoms := by
        intro hs
        have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, hs (hsub hPB0.2.1)⟩
        rw [hPQ] at hu
        exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
      have hrQ' : G.molecule.IsBlockGap L base κ Q.atoms cj rQ := hQu ▸ hrQ
      exact union_subset hsub (sg_block_absorbed_by_container hfam hM L γ η base c0 κ hκ hc0 Q C hQB0
        hCB hcQ (Or.inl hQu.symm) (hsub hcP) hcCj hrQ' hkQ hrC hkC hCQ)
    · right; left
      have hCh : ∃ R, C.shape = .hyper R := by
        rcases hh : C.shape with h | R
        · exact absurd ⟨h, hh⟩ hCvc
        · exact ⟨R, rfl⟩
      refine ⟨C, hCk, ?_, hCh, hCF⟩
      refine union_subset hsub ?_
      by_contra hQC
      have hCQ : ¬ C.atoms ⊆ Q.atoms := by
        intro hs
        have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, hs (hsub hPB0.2.1)⟩
        rw [hPQ] at hu
        exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
      exact object_hyper_overlap_nested hfam hM Q C hCh ⟨cj, mem_inter.mpr ⟨hcQ, hsub hcP⟩⟩ hQC hCQ
  · right; right
    by_cases hQW : Q.atoms ⊆ D.first ∪ D.second
    · exact ⟨D, union_subset hPD hQW, hDF⟩
    have hdeg := isDVPrime_degree_profile G.molecule hM D.first_vine D.second_vine D.sigma_one D.overlap
    have huv : D.upper ≠ D.lower := (isBlock_of_isSomeVine D.first_vine).2.2.2.1
    obtain ⟨nQ, hQch0⟩ := object_vc_chain Q hQvc
    have hconn := chain_connected hQch0
    have hex := dv_exit_contains_joints G.molecule hM huv hdeg.1 hdeg.2.1 hdeg.2.2 hQB0 hconn hQW
      ⟨cj, mem_inter.mpr ⟨hcQ, hPD hcP⟩⟩
    have hmiss : ¬(D.upper ∈ P.atoms ∧ D.lower ∈ P.atoms) := by
      rintro ⟨h1, h2⟩
      have a1 : D.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h1, hex.1⟩
      have a2 : D.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h2, hex.2⟩
      rw [hPQ] at a1 a2
      exact huv ((mem_singleton.mp a1).trans (mem_singleton.mp a2).symm)
    obtain ⟨hh, _⟩ := hPvc
    have hbr : ∃ A0, IsSomeVine γv G.molecule A0 D.upper D.lower ∧ P.atoms ⊆ A0 ∧
        A0 ⊆ D.first ∪ D.second := by
      rcases VC_in_DVPrime_missing_joint_side hfam G.molecule hM D.first_vine D.second_vine D.sigma_one D.overlap
        hh hPD hmiss with h | h
      · exact ⟨D.first, D.first_vine, h, subset_union_left⟩
      · exact ⟨D.second, D.second_vine, h, subset_union_right⟩
    obtain ⟨A0, hA0, hPA, hA0W⟩ := hbr
    have hQA : ¬ Q.atoms ⊆ A0 := fun h => hQW (h.trans hA0W)
    have hAQ : ¬ A0 ⊆ Q.atoms := by
      intro h
      have hu : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB0.2.1, h (hPA hPB0.2.1)⟩
      rw [hPQ] at hu
      exact hPB0.2.2.2.1 ((mem_singleton.mp hu).trans hPl.symm)
    obtain ⟨D'', h1, h2⟩ := (dv_branch_double_vine hfam G hM hA0 D.sigma_one
      hQvc hex.1 hex.2 hQA hAQ (hPA hcP) hcQ)
    refine ⟨D'', by rw [h1, h2]; exact union_subset (hPA.trans subset_union_left) subset_union_right, ?_⟩
    rw [h1, h2]
    exact disjointF_union (disjointF_of_subset hA0W hDF) hQF

end WaveTurbulence.GammaLow.Famc
