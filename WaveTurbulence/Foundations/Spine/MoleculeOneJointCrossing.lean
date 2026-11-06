/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.MoleculeOverlapCrossings
import Mathlib.Tactic

/-!
# Extra overlap beyond one common joint forces crossed other joints

DH23 Lemma 4.11(3), using the source connected-interior premise and the
actual incidence codes only through the realized degree profile.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- A proper overlap with any connected group meets a realized joint. -/
theorem group_overlap_contains_joint (hM : M.IsMolecule) {A B : Finset V} {b1 b2 : V}
    (hcA : GroupConnected M A) (RB : BlockRealization M B b1 b2)
    (hne : (A ∩ B).Nonempty) (hnot : ¬ A ⊆ B) :
    ∃ z ∈ A ∩ B, z = b1 ∨ z = b2 := by
  have hproper : ¬ A ⊆ A ∩ B := by
    intro h
    apply hnot
    intro x hx
    exact (Finset.mem_inter.mp (h hx)).2
  obtain ⟨u,hu,v,hv,hvnot,hadj⟩ := connected_group_boundary M
    (Finset.inter_subset_left : A ∩ B ⊆ A) hne hproper hcA.2
  have hvB : v ∉ B := fun hh => hvnot (Finset.mem_inter.mpr ⟨hv,hh⟩)
  exact ⟨u,hu,realized_entry_is_joint M hM RB hvB (Finset.mem_inter.mp hu).2 (adj_symmetric M hadj)⟩

/-- With just one common joint, any additional overlap forces the other
joint of B to be an interior atom of A. -/
theorem one_joint_extra_forces_crossing (hM : M.IsMolecule) {A B : Finset V} {a b c : V}
    (RA : BlockRealization M A a c) (RB : BlockRealization M B b c) (hab : a ≠ b)
    (hnotA : ¬ A ⊆ B) (hextra : ∃ u ∈ A ∩ B, u ≠ c)
    (hinterior : ∀ u ∈ A \ {a,c}, ∀ v ∈ A \ {a,c},
      (induced M (A \ {a,c})).SameComponent u v) : b ∈ A := by
  have hcB := RB.joints_mem_ne.2.1
  have hproper : A ≠ {a,c} := by
    intro he
    have haB : a ∈ B := by
      obtain ⟨u,hu,huc⟩ := hextra
      have huA := (Finset.mem_inter.mp hu).1
      rw [he] at huA
      simp only [Finset.mem_insert,Finset.mem_singleton] at huA
      rcases huA with hua | huc'
      · exact hua ▸ (Finset.mem_inter.mp hu).2
      · exact (huc huc').elim
    apply hnotA
    rw [he]
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact haB
    · exact hcB
  let I := A \ {a,c}
  have hcommon : ∃ z ∈ I, z ∈ B := by
    obtain ⟨u,hu,huc⟩ := hextra
    obtain ⟨huA,huB⟩ := Finset.mem_inter.mp hu
    by_cases hua : u = a
    · subst u
      obtain ⟨z,hzA,hza,hzc,hadj⟩ := realized_joint_interior_neighbor M RA hproper
      have hzB := realized_interior_adj_mem M hM RB huB hab RA.joints_mem_ne.2.2 hadj
      refine ⟨z,Finset.mem_sdiff.mpr ⟨hzA,?_⟩,hzB⟩
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using And.intro hza hzc
    · refine ⟨u,Finset.mem_sdiff.mpr ⟨huA,?_⟩,huB⟩
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using And.intro hua huc
  have hchoice : b ∈ A ∨ ∃ v ∈ I, v ∉ B := by
    obtain ⟨v,hvA,hvB⟩ := Finset.not_subset.mp hnotA
    have hvc : v ≠ c := fun he => hvB (he.symm ▸ hcB)
    by_cases hva : v = a
    · subst v
      obtain ⟨z,hzA,hza,hzc,hadj⟩ := realized_joint_interior_neighbor M RA hproper
      by_cases hzB : z ∈ B
      · rcases realized_entry_is_joint M hM RB hvB hzB hadj with hzb | hzc'
        · exact Or.inl (hzb ▸ hzA)
        · exact (hzc hzc').elim
      · right
        refine ⟨z,Finset.mem_sdiff.mpr ⟨hzA,?_⟩,hzB⟩
        simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using And.intro hza hzc
    · right
      refine ⟨v,Finset.mem_sdiff.mpr ⟨hvA,?_⟩,hvB⟩
      simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using And.intro hva hvc
  rcases hchoice with hbA | ⟨v,hvI,hvB⟩
  · exact hbA
  · obtain ⟨z,hzI,hzB⟩ := hcommon
    have hcI : GroupConnected M I := ⟨⟨z,hzI⟩,hinterior⟩
    have hnotI : ¬ I ⊆ B := fun hi => hvB (hi hvI)
    obtain ⟨u,hu,huj⟩ := group_overlap_contains_joint M hM hcI RB
      ⟨z,Finset.mem_inter.mpr ⟨hzI,hzB⟩⟩ hnotI
    have huI := (Finset.mem_inter.mp hu).1
    rcases huj with hub | huc
    · exact hub ▸ (Finset.mem_sdiff.mp huI).1
    · exact ((Finset.mem_sdiff.mp huI).2 (by simp [huc])).elim

end WaveTurbulence.Mole
