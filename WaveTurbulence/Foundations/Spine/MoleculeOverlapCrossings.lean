/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBlockRealizations
import Mathlib.Tactic

/-! # Joint crossings forced by overlapping realized blocks (DH23 Lemma 4.11) -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Full realized interiors cannot have any edge leaving the group. -/
theorem realized_interior_adj_mem (hM : M.IsMolecule) {S : Finset V} {a b u v : V}
    (R : BlockRealization M S a b) (hu : u ∈ S) (h1 : u ≠ a) (h2 : u ≠ b)
    (hadj : M.Adj u v) : v ∈ S := by
  obtain ⟨x,hx,hv⟩ := hadj
  rw [← hv]
  exact full_degree_no_exit M hM (R.atoms_subset hu) (R.degrees.2.2 u hu h1 h2) hx

/-- An outside edge enters a realized block/hyper-block at a joint. -/
theorem realized_entry_is_joint (hM : M.IsMolecule) {S : Finset V} {a b u v : V}
    (R : BlockRealization M S a b) (hu : u ∉ S) (hv : v ∈ S) (hadj : M.Adj u v) : v = a ∨ v = b := by
  by_cases h1 : v = a
  · exact Or.inl h1
  · by_cases h2 : v = b
    · exact Or.inr h2
    · exact (hu (realized_interior_adj_mem M hM R hv h1 h2 (adj_symmetric M hadj))).elim

/-- A proper overlap forces at least one joint of B to lie inside A. -/
theorem overlap_contains_joint (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hne : (A ∩ B).Nonempty) (hnot : ¬ A ⊆ B) :
    ∃ z ∈ A ∩ B, z = b1 ∨ z = b2 := by
  have hproper : ¬ A ⊆ A ∩ B := by
    intro h
    apply hnot
    intro x hx
    exact (Finset.mem_inter.mp (h hx)).2
  obtain ⟨u,hu,v,hv,hvnot,hadj⟩ := connected_group_boundary M
    (Finset.inter_subset_left : A ∩ B ⊆ A) hne hproper RA.connected.2
  have hvB : v ∉ B := fun hh => hvnot (Finset.mem_inter.mpr ⟨hv,hh⟩)
  refine ⟨u,hu,?_⟩
  exact realized_entry_is_joint M hM RB hvB (Finset.mem_inter.mp hu).2 (adj_symmetric M hadj)

/-- Four cross-interior joints would make the entire union saturated. -/
theorem not_all_joints_cross (hM : M.IsMolecule) {A B : Finset V} {a1 a2 b1 b2 : V}
    (RA : BlockRealization M A a1 a2) (RB : BlockRealization M B b1 b2)
    (hj : Disjoint ({a1,a2} : Finset V) {b1,b2})
    (ha1 : a1 ∈ B) (ha2 : a2 ∈ B) (hb1 : b1 ∈ A) (hb2 : b2 ∈ A) : False := by
  have hfull : ∀ z ∈ A ∪ B, M.degIn (A ∪ B) z = 4 := by
    intro z hz
    have hzM := (Finset.mem_union.mp hz).elim (fun hh => RA.atoms_subset hh) (fun hh => RB.atoms_subset hh)
    have hle := (degIn_le_deg M (A ∪ B) z).trans (deg_le_four M hM hzM)
    have hge : 4 ≤ M.degIn (A ∪ B) z := by
      rcases Finset.mem_union.mp hz with hzA | hzB
      · by_cases hza : z = a1 ∨ z = a2
        · have hzB : z ∈ B := hza.elim (fun he => he.symm ▸ ha1) (fun he => he.symm ▸ ha2)
          have hzjA : z ∈ ({a1,a2}:Finset V) := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hza
          have hzb : z ≠ b1 ∧ z ≠ b2 := by
            constructor <;> intro he <;> apply Finset.disjoint_left.mp hj hzjA <;> simp [he]
          have hd := RB.degrees.2.2 z hzB hzb.1 hzb.2
          have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
          omega
        · have hn : z ≠ a1 ∧ z ≠ a2 := not_or.mp hza
          have hd := RA.degrees.2.2 z hzA hn.1 hn.2
          have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
          omega
      · by_cases hzb : z = b1 ∨ z = b2
        · have hzA : z ∈ A := hzb.elim (fun he => he.symm ▸ hb1) (fun he => he.symm ▸ hb2)
          have hzjB : z ∈ ({b1,b2}:Finset V) := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hzb
          have hza : z ≠ a1 ∧ z ≠ a2 := by
            constructor <;> intro he <;> apply Finset.disjoint_right.mp hj hzjB <;> simp [he]
          have hd := RA.degrees.2.2 z hzA hza.1 hza.2
          have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
          omega
        · have hn : z ≠ b1 ∧ z ≠ b2 := not_or.mp hzb
          have hd := RB.degrees.2.2 z hzB hn.1 hn.2
          have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
          omega
    omega
  exact no_saturated_group M hM
    (by intro z hz; exact (Finset.mem_union.mp hz).elim (fun hh => RA.atoms_subset hh) (fun hh => RB.atoms_subset hh))
    ⟨a1,Finset.mem_union_left B RA.joints_mem_ne.1⟩ hfull

/-- Each joint of a proper realized block has a neighbor in its interior:
strictly fewer than all joint incidences can join the other joint. -/
theorem realized_joint_interior_neighbor {S : Finset V} {a b : V}
    (R : BlockRealization M S a b) (hproper : S ≠ {a,b}) :
    ∃ z ∈ S, z ≠ a ∧ z ≠ b ∧ M.Adj a z := by
  classical
  have hj := R.joints_mem_ne
  have hno : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a := by
    intro x hx
    have hh := R.no_joint_loop x (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hd := R.degrees.1
  have hs := R.sigma_lt_jointDegree hproper
  have hp := degIn_pair_eq_bondsBetween M hj.2.2 hno
  change M.degIn {a,b} a = M.sigma a b at hp
  have hlt : M.degIn {a,b} a < M.degIn S a := by omega
  have hex : ∃ x ∈ (M.dartsAt a).filter (M.InGroup S),
      x ∉ (M.dartsAt a).filter (M.InGroup {a,b}) := by
    by_contra h
    push Not at h
    have hc := Finset.card_le_card (show (M.dartsAt a).filter (M.InGroup S) ⊆
      (M.dartsAt a).filter (M.InGroup {a,b}) from h)
    change M.degIn S a ≤ M.degIn {a,b} a at hc
    omega
  obtain ⟨x,hx,hxnot⟩ := hex
  obtain ⟨hxv,hxa,hxm⟩ := Finset.mem_filter.mp hx
  have hax := (mem_dartsAt M a x).mp hxv
  have hnot : M.atom (M.mate x) ≠ a ∧ M.atom (M.mate x) ≠ b := by
    constructor <;> intro he <;> apply hxnot <;> apply Finset.mem_filter.mpr
    · exact ⟨hxv,by simp [Molecule.InGroup,hax,he]⟩
    · exact ⟨hxv,by simp [Molecule.InGroup,hax,he]⟩
  exact ⟨M.atom (M.mate x),hxm,hnot.1,hnot.2,⟨x,hax,rfl⟩⟩

end WaveTurbulence.Mole
