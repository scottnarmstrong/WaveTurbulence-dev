/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDVContainer
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVDegrees
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineDVMissingJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceDiamondContradiction
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceUnionDV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.DV
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceDVContainer`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 One-joint union of two ordinary objects when P lies in a double vine and Q leaves it: Q
contains both double-vine joints (flux), P lies in one branch, and the overlap classification of
that branch with Q puts the union inside a new double vine. 

**Low-range change (L6-HDS).** A vine whose joints are joined by a bond is a double bond or a T-vine with `σ = 1`
(`DS.vineEnl_joint_bond_cases`; main: (I) or (V)); the double vine built from two such vines is a DV′ of the low family
(`Src.DoubleVine`, with `σ = 1`).
-/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

/-- Q contains both joints of the vine A0 (a DV′ branch, `σ = 1`) (a branch inside W) but is not inside W; P is in A0
and meets Q only in cj: then A0 and Q form a double vine. -/
theorem dv_branch_double_vine {w : ℕ} (G : Garden w) (hM : G.molecule.IsMolecule)
    {A0 : Finset (GBranch G.tree)} {u v : GBranch G.tree} (hσ : G.molecule.sigma u v = 1)
    (hA0 : Src.IsSomeVine Src.γL G.molecule A0 u v)
    {Q : Src.Object Src.γL G.molecule} (hQvc : ∃ h, Q.shape = .vc h)
    (huQ : u ∈ Q.atoms) (hvQ : v ∈ Q.atoms) (hQA : ¬ Q.atoms ⊆ A0) (hAQ : ¬ A0 ⊆ Q.atoms)
    {cj : GBranch G.tree} (hcA : cj ∈ A0) (hcQ : cj ∈ Q.atoms) :
    ∃ D'' : Src.DoubleVine Src.γL G, D''.first = A0 ∧ D''.second = Q.atoms := by
  have hQB := object_vc_block Q hQvc
  obtain ⟨nQ, hQch⟩ := object_vc_chain Q hQvc
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises (Src.Object.ofVine hA0)
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises Q
  obtain ⟨_, _, hcl⟩ := Mole.molecule_overlap_classification G.molecule hM RA RB
    ⟨cj, mem_inter.mpr ⟨hcA, hcQ⟩⟩ hAQ hQA hdA hdB hiA hiB
  have hAB : A0 ∩ Q.atoms ⊇ {u, v} := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact mem_inter.mpr ⟨hA0.block.2.1, huQ⟩
    · rw [mem_singleton.mp hx]; exact mem_inter.mpr ⟨hA0.block.2.2.1, hvQ⟩
  have huv : u ≠ v := hA0.block.2.2.2.1
  rcases hcl with ⟨h1, h2, _, _⟩ | ⟨_, _, a, b, c, _, _, _, _, _, h5, _⟩ | ⟨hdis, ⟨T⟩⟩
  · -- same joints
    have h2' : A0 ∩ Q.atoms = {u, v} := h2
    have hQB' : G.molecule.IsBlock Q.atoms u v ∧ Src.Chain Src.γL G.molecule Q.atoms u v nQ := by
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
    obtain ⟨z, hza, hzb, hzA, hzQ⟩ := diamond_shared_bond hM hA0.block hQB'.1 h2'
    have hXQ0 := chain_single_of_joint_bond hM hQB'.2.toVine hQB'.1 hza hzb hzQ
    have hXQ : G.molecule.IsTVine Q.atoms u v := by
      rcases DS.vineEnl_joint_bond_cases hXQ0 hza hzb with h | h
      · exfalso
        apply hQA
        rw [Vine.typeI_atoms h]
        intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact hA0.block.2.1
        · rw [mem_singleton.mp hx]; exact hA0.block.2.2.1
      · exact h.1
    exact ⟨⟨A0, Q.atoms, u, v, hσ, hA0, Src.isSomeVine_of_T hXQ, h2'⟩, rfl, rfl⟩
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

end WaveTurbulence.GammaLow.FinalCount.H
