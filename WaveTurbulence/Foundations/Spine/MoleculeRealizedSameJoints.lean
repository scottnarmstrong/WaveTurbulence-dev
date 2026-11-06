/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockRealizations
import Mathlib.Tactic

/-!
# DH23 Lemma 4.11(a), including exclusion of hyper-blocks

The realizations are actual blocks or hyper-blocks with connected adjoints.
The argument uses full-degree barriers, actual joint incidence counts and
the no-saturated-component axiom; no overlap conclusion is assumed.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- The two-joint degree profile and the interior path condition force the
intersection to contain only the shared joints, even for hyper-blocks. -/
theorem realized_same_joints_intersection (hM : M.IsMolecule) {A B : Finset V} {a b : V}
    (RA : BlockRealization M A a b) (RB : BlockRealization M B a b) (hnot : ¬ A ⊆ B)
    (hconn : ∀ u ∈ A \ {a,b}, ∀ v ∈ A \ {a,b},
      (induced M (A \ {a,b})).SameComponent u v) : A ∩ B = {a,b} := by
  have hA := RA.joints_mem_ne
  have hB := RB.joints_mem_ne
  ext u
  constructor
  · intro hu
    obtain ⟨huA,huB⟩ := Finset.mem_inter.mp hu
    by_contra hj
    have huT : u ∈ A \ {a,b} := Finset.mem_sdiff.mpr ⟨huA,hj⟩
    obtain ⟨v,hvA,hvB⟩ := Finset.not_subset.mp hnot
    have hvT : v ∈ A \ {a,b} := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hvA,?_⟩
      intro hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hvB hB.1
      · exact hvB hB.2.1
    have hd : ∀ z ∈ B, z ∈ A \ {a,b} → M.degIn B z = 4 := by
      intro z hz hzT
      have hn := (Finset.mem_sdiff.mp hzT).2
      have hz1 : z ≠ a := fun he => hn (Finset.mem_insert.mpr (Or.inl he))
      have hz2 : z ≠ b := fun he => hn (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he)))
      exact RB.degrees.2.2 z hz hz1 hz2
    exact hvB ((induced_path_barrier M hM RB.atoms_subset hd (hconn u huT v hvT)).mp huB)
  · intro hu
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hA.1,hB.1⟩
    · exact Finset.mem_inter.mpr ⟨hA.2.1,hB.2.1⟩

/-- Degree two distinguishes an actual block from a hyper-block realization. -/
theorem BlockRealization.isBlock_of_jointDegree_two {S : Finset V} {a b : V}
    (R : BlockRealization M S a b) (hd : R.jointDegree = 2) : M.IsBlock S a b := by
  cases R with
  | block hB hc => exact hB
  | hyper e he hB hc => cases hd

/-- DH23 Lemma 4.11(a), for both possible source input types: the groups
are blocks, their intersection is the two joints, and sigma=1. -/
theorem realized_same_joints_classification (hM : M.IsMolecule) {A B : Finset V} {a b : V}
    (RA : BlockRealization M A a b) (RB : BlockRealization M B a b)
    (hnotA : ¬ A ⊆ B) (hnotB : ¬ B ⊆ A)
    (hconn : ∀ u ∈ A \ {a,b}, ∀ v ∈ A \ {a,b},
      (induced M (A \ {a,b})).SameComponent u v) :
    M.IsBlock A a b ∧ M.IsBlock B a b ∧ A ∩ B = {a,b} ∧ M.sigma a b = 1 := by
  have hi := realized_same_joints_intersection M hM RA RB hnotA hconn
  have ha := RA.joints_mem_ne
  have hb := RB.joints_mem_ne
  have hproperA : A ≠ {a,b} := by
    intro he
    apply hnotA
    rw [he]
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hb.1
    · exact hb.2.1
  have hproperB : B ≠ {a,b} := by
    intro he
    apply hnotB
    rw [he]
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha.1
    · exact ha.2.1
  have hsigA := RA.sigma_lt_jointDegree hproperA
  have hsigB := RB.sigma_lt_jointDegree hproperB
  have hnoa : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a := by
    intro x hx
    have hh := RA.no_joint_loop x (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hnob : ∀ x, M.atom x = b → M.atom (M.mate x) ≠ b := by
    intro x hx
    have hh := RA.no_joint_loop x (Or.inr hx)
    rw [hx] at hh
    exact hh
  have hda : M.degIn (A ∩ B) a = M.sigma a b := by
    rw [hi,degIn_pair_eq_bondsBetween M ha.2.2 hnoa]
    rfl
  have hdb : M.degIn (A ∩ B) b = M.sigma a b := by
    rw [hi,Finset.pair_comm,degIn_pair_eq_bondsBetween M (Ne.symm ha.2.2) hnob,bondsBetween_symm]
    rfl
  have huA := degIn_union_add_inter M A B ha.1 hb.1
  have huB := degIn_union_add_inter M A B ha.2.1 hb.2.1
  obtain ⟨hdAa,hdAb,hdAi⟩ := RA.degrees
  obtain ⟨hdBa,hdBb,hdBi⟩ := RB.degrees
  rw [hda,hdAa,hdBa] at huA
  rw [hdb,hdAb,hdBb] at huB
  have heq : M.degIn (A ∪ B) a = M.degIn (A ∪ B) b := by omega
  have hle : M.degIn (A ∪ B) a ≤ 4 :=
    (degIn_le_deg M (A ∪ B) a).trans (deg_le_four M hM (RA.atoms_subset ha.1))
  have hne4 : M.degIn (A ∪ B) a ≠ 4 := by
    intro h4
    have hfull : ∀ z ∈ A ∪ B, M.degIn (A ∪ B) z = 4 := by
      intro z hz
      by_cases hza : z = a
      · subst z
        exact h4
      · by_cases hzb : z = b
        · subst z
          exact heq.symm.trans h4
        · have hzM := (Finset.mem_union.mp hz).elim
            (fun hh => RA.atoms_subset hh) (fun hh => RB.atoms_subset hh)
          have hmax := (degIn_le_deg M (A ∪ B) z).trans (deg_le_four M hM hzM)
          have hmin : 4 ≤ M.degIn (A ∪ B) z := by
            rcases Finset.mem_union.mp hz with hzA | hzB
            · have h4 := hdAi z hzA hza hzb
              have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
              omega
            · have h4 := hdBi z hzB hza hzb
              have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
              omega
          omega
    exact no_saturated_group M hM
      (by intro z hz; exact (Finset.mem_union.mp hz).elim (fun hh => RA.atoms_subset hh) (fun hh => RB.atoms_subset hh))
      ⟨a,Finset.mem_union_left B ha.1⟩ hfull
  have hcasesA := RA.jointDegree_cases
  have hcasesB := RB.jointDegree_cases
  have hdA : RA.jointDegree = 2 := by omega
  have hdB : RB.jointDegree = 2 := by omega
  refine ⟨BlockRealization.isBlock_of_jointDegree_two M RA hdA,BlockRealization.isBlock_of_jointDegree_two M RB hdB,hi,?_⟩
  omega

end WaveTurbulence.Mole
