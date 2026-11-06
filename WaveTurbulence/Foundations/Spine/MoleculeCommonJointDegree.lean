/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeSingleDeficit
public import WaveTurbulence.Foundations.Spine.MoleculeRealizedSameJoints
import Mathlib.Tactic

/-!
# The common joint in a hypothetical nontrivial one-joint overlap

DH23 Lemma 4.11(3): if the two other joints lie inside the opposite groups,
every atom of the union except the common joint is full. Handshaking and
absence of saturation force the common joint to have degree two.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The exact common-joint degree in the hypothetical crossed one-joint case. -/
theorem common_crossed_degree_two (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c)
    (hab : a ≠ b) (haB : a ∈ B) (hbA : b ∈ A) : M.degIn (A ∪ B) c = 2 := by
  have hU : A ∪ B ⊆ M.atoms := by
    intro z hz
    exact (Finset.mem_union.mp hz).elim (fun hh => RA.atoms_subset hh) (fun hh => RB.atoms_subset hh)
  have hcU := Finset.mem_union_left B RA.joints_mem_ne.2.1
  have hmin : 2 ≤ M.degIn (A ∪ B) c := by
    have hd := RA.degrees.2.1
    have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) c
    have hcases := RA.jointDegree_cases
    omega
  apply single_deficit_degree_two M hM hU hcU hmin
  intro z hz hzc
  have hmax := (degIn_le_deg M (A ∪ B) z).trans (deg_le_four M hM (hU hz))
  have hmin : 4 ≤ M.degIn (A ∪ B) z := by
    rcases Finset.mem_union.mp hz with hzA | hzB
    · by_cases hza : z = a
      · subst z
        have hd := RB.degrees.2.2 a haB hab RA.joints_mem_ne.2.2
        have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) a
        omega
      · have hd := RA.degrees.2.2 z hzA hza hzc
        have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
        omega
    · by_cases hzb : z = b
      · subst z
        have hd := RA.degrees.2.2 b hbA (Ne.symm hab) RB.joints_mem_ne.2.2
        have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) b
        omega
      · have hd := RB.degrees.2.2 z hzB hzb hzc
        have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
        omega
  omega

/-- Both realizations in that configuration are ordinary blocks. -/
theorem common_crossed_are_blocks (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c)
    (hab : a ≠ b) (haB : a ∈ B) (hbA : b ∈ A) : M.IsBlock A a c ∧ M.IsBlock B b c := by
  have hd := common_crossed_degree_two M hM RA RB hab haB hbA
  have hRA := RA.degrees.2.1
  have hRB := RB.degrees.2.1
  have hma := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) c
  have hmb := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) c
  have hca := RA.jointDegree_cases
  have hcb := RB.jointDegree_cases
  have h2a : RA.jointDegree = 2 := by omega
  have h2b : RB.jointDegree = 2 := by omega
  exact ⟨BlockRealization.isBlock_of_jointDegree_two M RA h2a,
    BlockRealization.isBlock_of_jointDegree_two M RB h2b⟩

/-- The common joint cannot connect to the part of A outside B: its two
incidences are already shared by the two blocks. -/
theorem common_crossed_no_exterior_edge (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c)
    (hab : a ≠ b) (haB : a ∈ B) (hbA : b ∈ A) :
    ∀ p ∈ A \ B, ¬ M.Adj c p := by
  obtain ⟨hA,hB⟩ := common_crossed_are_blocks M hM RA RB hab haB hbA
  have hd := common_crossed_degree_two M hM RA RB hab haB hbA
  have hdc := (block_joint_degrees M hB).2
  have he : (M.dartsAt c).filter (M.InGroup B) = (M.dartsAt c).filter (M.InGroup (A ∪ B)) :=
    internal_darts_eq_of_degree_eq M (Finset.subset_union_right : B ⊆ A ∪ B) c (hdc.trans hd.symm)
  intro p hp hadj
  obtain ⟨hpA,hpB⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨x,hxc,hxp⟩ := hadj
  have hx : x ∈ (M.dartsAt c).filter (M.InGroup (A ∪ B)) := Finset.mem_filter.mpr
    ⟨(mem_dartsAt M c x).mpr hxc,hxc.symm ▸ Finset.mem_union_right A hB.2.2.1,
      hxp.symm ▸ Finset.mem_union_left B hpA⟩
  rw [← he] at hx
  exact hpB (hxp ▸ (Finset.mem_filter.mp hx).2.2)

end WaveTurbulence.Mole
