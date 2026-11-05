/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
import Mathlib.Tactic

/-! # DH23 Lemma 4.11: complete common-joint case for connected blocks -/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- A connected group is determined by a nonempty internal subset already
containing every incidence at each of its atoms. -/
theorem connected_group_eq_of_degrees {A B : Finset V} (hAB : A ⊆ B) (hne : A.Nonempty)
    (hc : GroupConnected M B) (hd : ∀ u ∈ A, M.degIn A u = M.degIn B u) : A = B := by
  classical
  apply Finset.Subset.antisymm hAB
  by_contra hproper
  obtain ⟨u,hu,v,hv,hvout,x,hxu,hxv⟩ := connected_group_boundary M hAB hne hproper hc.2
  have he : (M.dartsAt u).filter (M.InGroup A) = (M.dartsAt u).filter (M.InGroup B) := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨hyu,hya,hym⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyu,hAB hya,hAB hym⟩
    · exact (hd u hu).ge
  have hx : x ∈ (M.dartsAt u).filter (M.InGroup B) :=
    Finset.mem_filter.mpr ⟨(mem_dartsAt M u x).mpr hxu,hxu.symm ▸ hAB hu,hxv.symm ▸ hv⟩
  rw [← he] at hx
  exact hvout (hxv ▸ (Finset.mem_filter.mp hx).2.2)

/-- A connected block with sigma=2 is exactly its two joints. -/
theorem connected_block_eq_pair_of_sigma_two {S : Finset V} {a b : V}
    (hB : M.IsBlock S a b) (hc : GroupConnected M S) (hs : M.sigma a b = 2) : S = {a,b} := by
  have hne := hB.2.2.2.1
  have hnoa : ∀ x, M.atom x = a → M.atom (M.mate x) ≠ a := by
    intro x hx
    have hh := connected_block_no_joint_loop M hB hc (Or.inl hx)
    rw [hx] at hh
    exact hh
  have hnob : ∀ x, M.atom x = b → M.atom (M.mate x) ≠ b := by
    intro x hx
    have hh := connected_block_no_joint_loop M hB hc (Or.inr hx)
    rw [hx] at hh
    exact hh
  have hsub : {a,b} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hB.2.1
    · exact hB.2.2.1
  apply Eq.symm
  apply connected_group_eq_of_degrees M hsub (Finset.insert_nonempty _ _) hc
  intro u hu
  simp only [Finset.mem_insert,Finset.mem_singleton] at hu
  obtain ⟨h1,h2⟩ := block_joint_degrees M hB
  rcases hu with rfl | rfl
  · rw [degIn_pair_eq_bondsBetween M hne hnoa,h1]
    exact hs
  · rw [Finset.pair_comm,degIn_pair_eq_bondsBetween M (Ne.symm hne) hnob,h2,bondsBetween_symm]
    exact hs

/-- DH23 Lemma 4.11(a): under the explicit connected-block convention,
incomparable blocks with the same joints share only those joints, and
have exactly one bond between them. -/
theorem block_same_joints_classification (hM : M.IsMolecule) {A B : Finset V} {a b : V}
    (hA : M.IsBlock A a b) (hB : M.IsBlock B a b) (hc : GroupConnected M A)
    (hnot : ¬ A ⊆ B)
    (hinterior : ∀ u ∈ A \ {a,b}, ∀ v ∈ A \ {a,b},
      (induced M (A \ {a,b})).SameComponent u v) :
    A ∩ B = {a,b} ∧ M.sigma a b = 1 := by
  have hi := block_same_joints_intersection M hM hA hB hnot hinterior
  refine ⟨hi,?_⟩
  have hsle := block_sigma_le_two M hA
  have hsne2 : M.sigma a b ≠ 2 := by
    intro hs
    have he := connected_block_eq_pair_of_sigma_two M hA hc hs
    apply hnot
    rw [he]
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hB.2.1
    · exact hB.2.2.1
  have hsne0 : M.sigma a b ≠ 0 := by
    intro hs
    have hno (z : V) (hz : z = a ∨ z = b) : ∀ x, M.atom x = z → M.atom (M.mate x) ≠ z := by
      intro x hx
      have hh := connected_block_no_joint_loop M hA hc
        (hz.elim (fun he => Or.inl (hx.trans he)) (fun he => Or.inr (hx.trans he)))
      rw [hx] at hh
      exact hh
    have hda : M.degIn (A ∩ B) a = 0 := by
      rw [hi,degIn_pair_eq_bondsBetween M hA.2.2.2.1 (hno a (Or.inl rfl))]
      exact hs
    have hdb : M.degIn (A ∩ B) b = 0 := by
      rw [hi,Finset.pair_comm,degIn_pair_eq_bondsBetween M (Ne.symm hA.2.2.2.1) (hno b (Or.inr rfl)),bondsBetween_symm]
      exact hs
    have hfull : ∀ z ∈ A ∪ B, M.degIn (A ∪ B) z = 4 := by
      intro z hz
      by_cases hza : z = a
      · subst z
        have he := degIn_union_add_inter M A B hA.2.1 hB.2.1
        have h1 := (block_joint_degrees M hA).1
        have h2 := (block_joint_degrees M hB).1
        omega
      · by_cases hzb : z = b
        · subst z
          have he := degIn_union_add_inter M A B hA.2.2.1 hB.2.2.1
          have h1 := (block_joint_degrees M hA).2
          have h2 := (block_joint_degrees M hB).2
          omega
        · have hamb : z ∈ M.atoms := (Finset.mem_union.mp hz).elim (fun hz => hA.1 hz) (fun hz => hB.1 hz)
          have hle := (degIn_le_deg M (A ∪ B) z).trans (deg_le_four M hM hamb)
          have hge : 4 ≤ M.degIn (A ∪ B) z := by
            rcases Finset.mem_union.mp hz with hzA | hzB
            · have hd := hA.2.2.2.2.2.2.2.2.1 z hzA hza hzb
              have hm := degIn_mono M (Finset.subset_union_left : A ⊆ A ∪ B) z
              omega
            · have hd := hB.2.2.2.2.2.2.2.2.1 z hzB hza hzb
              have hm := degIn_mono M (Finset.subset_union_right : B ⊆ A ∪ B) z
              omega
          omega
    exact no_saturated_group M hM (by intro z hz; exact (Finset.mem_union.mp hz).elim (fun hz => hA.1 hz) (fun hz => hB.1 hz))
      ⟨a,Finset.mem_union_left B hA.2.1⟩ hfull
  omega

end WaveTurbulence.Mole
