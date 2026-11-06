/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
public import WaveTurbulence.Foundations.Spine.SourceBlockJointGaps
public import WaveTurbulence.Foundations.Molecule.VineSGJointExclusion
public import WaveTurbulence.Foundations.Molecule.VineNestedGaps
/-! An SG block through a non-joint atom of an LG/ZG block is contained in it
(overlap classification plus gap separation excludes the interleaved case). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sg_block_absorbed_by_container {M : Molecule V D} (hM : M.IsMolecule) {d : ℕ}
    (L γ η : ℝ) (w : Mom d) (c0 : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c0 κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c0 v = 0)
    (Q C : SourceVine.Object M) (hQB : M.IsBlock Q.atoms Q.upper Q.lower)
    (hCB : M.IsBlock C.atoms C.upper C.lower) {c : V}
    (hcQ : c ∈ Q.atoms) (hcQj : c = Q.upper ∨ c = Q.lower) (hcC : c ∈ C.atoms)
    (hcCj : c ≠ C.upper ∧ c ≠ C.lower)
    {rQ rC : Mom d} (hrQ : M.IsBlockGap L w κ Q.atoms c rQ)
    (hQsg : Molecule.gapKind L γ η rQ = .SG)
    (hrC : M.IsBlockGap L w κ C.atoms C.upper rC)
    (hCout : Molecule.gapKind L γ η rC = .LG ∨ Molecule.gapKind L γ η rC = .ZG)
    (hCQ : ¬ C.atoms ⊆ Q.atoms) : Q.atoms ⊆ C.atoms := by
  by_contra hQC
  obtain ⟨⟨RA⟩, hdA, hiA⟩ := object_overlap_premises Q
  obtain ⟨⟨RB⟩, hdB, hiB⟩ := object_overlap_premises C
  obtain ⟨_, _, hcl⟩ := Mole.molecule_overlap_classification M hM RA RB
    ⟨c, mem_inter.mpr ⟨hcQ, hcC⟩⟩ hQC hCQ hdA hdB hiA hiB
  rcases hcl with ⟨h1, _, _⟩ | ⟨_, _, a, b, c', h2, h3, _, _, _, h5, _⟩ | ⟨_, ⟨T⟩⟩
  · have : c ∈ ({C.upper, C.lower} : Finset V) := by
      rw [← h1]; rcases hcQj with h | h <;> simp [h]
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact hcCj.1 h
    · exact hcCj.2 h
  · have hc' : c ∈ ({c'} : Finset V) := h5 ▸ mem_inter.mpr ⟨hcQ, hcC⟩
    have : c' ∈ ({C.upper, C.lower} : Finset V) := by rw [h3]; simp
    have hcc := mem_singleton.mp hc'
    subst hcc
    simp only [mem_insert, mem_singleton] at this
    rcases this with h | h
    · exact hcCj.1 h
    · exact hcCj.2 h
  · -- interleaved case
    have hcin : c ∈ (T.C0 ∪ T.C1) ∩ (T.C1 ∪ T.C2) := by
      rw [← T.left_union, ← T.right_union]; exact mem_inter.mpr ⟨hcQ, hcC⟩
    have hcC1 : c ∈ T.C1 := by
      rcases mem_inter.mp hcin with ⟨h1, h2⟩
      rcases mem_union.mp h1 with h1 | h1
      · rcases mem_union.mp h2 with h2 | h2
        · exact h2
        · exact absurd h2 (Finset.disjoint_left.mp T.exterior_disjoint h1)
      · exact h1
    have hcj : c = T.p0 ∨ c = T.p2 := by
      have : c ∈ ({T.p0, T.p2} : Finset V) := by
        rw [← T.left_joints]; rcases hcQj with h | h <;> simp [h]
      simpa using this
    have hc2 : c = T.p2 := by
      rcases hcj with h | h
      · exfalso
        have h0 : T.p0 ∈ T.C0 := T.block0.2.1
        have h1 : T.p0 ∈ T.C1 := h ▸ hcC1
        have : T.p0 ∈ T.C0 ∩ T.C1 := mem_inter.mpr ⟨h0, h1⟩
        rw [T.left_inter] at this
        exact T.block0.2.2.2.1 (mem_singleton.mp this)
      · exact h
    subst hc2
    have hC1Q : T.C1 ⊆ Q.atoms := by
      intro x hx; rw [T.left_union]; exact mem_union_right _ hx
    have hC1C : T.C1 ⊆ C.atoms := by
      intro x hx; rw [T.right_union]; exact mem_union_left _ hx
    have hB1 : M.IsBlock T.C1 T.p2 T.p1 := Mole.block_swap_joints M T.block1
    have hQ' : M.IsBlock Q.atoms T.p2 T.p0 :=
      Mole.block_transport_joints M ((Finset.pair_comm _ _).trans T.left_joints.symm) hQB
    obtain ⟨r1, hr1⟩ := source_block_joint_gap_exists M hB1 (Or.inl rfl) L w κ
    have hr1eq : r1 = rQ := Vine.nested_block_gap_eq M hC1Q hB1 hQ' _ hr1 hrQ
    subst hr1eq
    have habs := Vine.SG_block_outer_joints_absent M hM hCB hB1 hC1C L γ η w c0 κ hκ hc0
      hrC hr1 hCout hQsg
    have hp1 : T.p1 ∈ ({C.upper, C.lower} : Finset V) := by
      have h := T.right_joints
      have : T.p1 ∈ ({T.p1, T.p3} : Finset V) := by simp
      rw [← h] at this; exact this
    have hp1C1 : T.p1 ∈ T.C1 := T.block1.2.1
    simp only [mem_insert, mem_singleton] at hp1
    rcases hp1 with h | h
    · exact habs.1 ((congrArg (fun z => z ∈ T.C1) h).mp hp1C1)
    · exact habs.2 ((congrArg (fun z => z ∈ T.C1) h).mp hp1C1)

end WaveTurbulence.LGSpine
