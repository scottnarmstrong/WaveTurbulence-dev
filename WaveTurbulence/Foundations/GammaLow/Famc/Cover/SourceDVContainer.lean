/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainBlock
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.DVFacts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceContainerAbsorb
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionContradiction
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceUnionEligible
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.VineDelObjects
public import WaveTurbulence.Foundations.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.Spine.SourceDVExit
public import WaveTurbulence.Foundations.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.Spine.MoleculeOverlapClassification
public import WaveTurbulence.Foundations.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineDVDegrees
/-! One-joint union of two ordinary objects when P lies in a double vine and Q leaves it: Q
contains both double-vine joints (flux), P lies in one branch, and the overlap classification of
that branch with Q puts the union inside a new double vine. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceDVContainer` (sha256 1e218370cdd175a9120d1c5f3483e9bc8b06f50cb515a81842fc89d5f541d868) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

/-- Q contains both joints of the V-vine A0 (a branch inside W) but is not inside W; P is in A0
and meets Q only in cj: then A0 and Q form a double vine. -/
theorem dv_branch_double_vine (hfam : FamFacts γv) {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule)
    {A0 : Finset (GBranch G.tree)} {u v : GBranch G.tree} (hA0 : IsSomeVine γv G.molecule A0 u v) (hσ : G.molecule.sigma u v = 1)
    {Q : Object γv G.molecule} (hQvc : ∃ h, Q.shape = .vc h)
    (huQ : u ∈ Q.atoms) (hvQ : v ∈ Q.atoms) (hQA : ¬ Q.atoms ⊆ A0) (hAQ : ¬ A0 ⊆ Q.atoms)
    {cj : GBranch G.tree} (hcA : cj ∈ A0) (hcQ : cj ∈ Q.atoms) :
    ∃ D'' : DoubleVine γv G, D''.first = A0 ∧ D''.second = Q.atoms := by
  have hQB := object_vc_block Q hQvc
  obtain ⟨nQ, hQch⟩ := object_vc_chain Q hQvc
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises hfam (Object.ofVine hA0)
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises hfam Q
  obtain ⟨_, _, hcl⟩ := Mole.molecule_overlap_classification G.molecule hM RA RB
    ⟨cj, mem_inter.mpr ⟨hcA, hcQ⟩⟩ hAQ hQA hdA hdB hiA hiB
  have hAB : A0 ∩ Q.atoms ⊇ {u, v} := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨(isBlock_of_isSomeVine hA0).2.1, huQ⟩
    · rw [mem_singleton.mp hx]; exact mem_inter.mpr ⟨(isBlock_of_isSomeVine hA0).2.2.1, hvQ⟩
  have huv : u ≠ v := (isBlock_of_isSomeVine hA0).2.2.2.1
  rcases hcl with ⟨h1, h2, _, _⟩ | ⟨_, _, a, b, c, _, _, _, _, _, h5, _⟩ | ⟨hdis, ⟨T⟩⟩
  · -- same joints
    have h2' : A0 ∩ Q.atoms = {u, v} := h2
    have hQB' : G.molecule.IsBlock Q.atoms u v ∧ Chain γv G.molecule Q.atoms u v nQ := by
      rcases Mole.finset_pair_eq_pair_iff.mp h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · have e1' : Q.upper = u := e1.symm
        have e2' : Q.lower = v := e2.symm
        have hB1 := hQB
        have hC1 := hQch
        rw [e1', e2'] at hB1 hC1
        exact ⟨hB1, hC1⟩
      · have e1' : Q.lower = u := e1.symm
        have e2' : Q.upper = v := e2.symm
        have hB1 := Mole.block_swap_joints _ hQB
        have hC1 := chain_swap hQch
        rw [e1', e2'] at hB1 hC1
        exact ⟨hB1, hC1⟩
    obtain ⟨z, hza, hzb, hzA, hzQ⟩ := diamond_shared_bond hM (isBlock_of_isSomeVine hA0) hQB'.1 h2'
    have hXQ := chain_single_of_joint_bond hM hQB'.2 hQB'.1 hza hzb hzQ
    exact ⟨⟨A0, Q.atoms, u, v, hσ, hA0, hXQ, h2'⟩, rfl, rfl⟩
  · have hu : u ∈ ({c} : Finset _) := by rw [← h5]; exact hAB (mem_insert_self _ _)
    have hv : v ∈ ({c} : Finset _) := by rw [← h5]; exact hAB (mem_insert_of_mem (mem_singleton_self _))
    exact absurd ((mem_singleton.mp hu).trans (mem_singleton.mp hv).symm) huv
  · exfalso
    have hp0 : T.p0 ∈ ({u, v} : Finset _) := by
      have : T.p0 ∈ ({T.p0, T.p2} : Finset _) := by simp
      rwa [← T.left_joints] at this
    have hp0Q : T.p0 ∈ Q.atoms := by
      rcases mem_insert.mp hp0 with h | h
      · rw [h]; exact huQ
      · rw [mem_singleton.mp h]; exact hvQ
    have hp0C1 : T.p0 ∈ T.C1 := by
      have hp0Q' : T.p0 ∈ T.C1 ∪ T.C2 := by rw [← T.right_union]; exact hp0Q
      rcases mem_union.mp hp0Q' with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp T.exterior_disjoint T.block0.2.1)
    have : T.p0 ∈ T.C0 ∩ T.C1 := mem_inter.mpr ⟨T.block0.2.1, hp0C1⟩
    rw [T.left_inter] at this
    have hp1 := mem_singleton.mp this
    have hA' := (Finset.ext_iff.mp T.left_joints T.p0).mpr (by simp)
    have hB' := (Finset.ext_iff.mp T.right_joints T.p1).mpr (by simp)
    rw [← hp1] at hB'
    exact Finset.disjoint_left.mp hdis hA' hB'

end WaveTurbulence.GammaLow.Famc
