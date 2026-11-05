/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.MoleculeGroupIdentities
import Mathlib.Tactic

/-!
# Connected block realizations and joint-loop exclusion

The draft degree-only block predicate is retained. For concatenation and
DH23 overlap classification, the atomic groups are explicitly connected;
without this condition an isolated loop can serve as a disconnected joint.
-/

public section
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] (M : Molecule V D)

/-- Actual undirected connectedness within an atomic group. -/
@[expose] def GroupConnected (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, (induced M S).SameComponent u v

/-- A degree-two atom in a connected group with another atom cannot have
a loop: that loop would consume both of its actual internal incidences. -/
theorem connected_degree_two_no_loop {S : Finset V} {v z : V}
    (hc : GroupConnected M S) (hv : v ∈ S) (hz : z ∈ S) (hne : z ≠ v)
    (hd : M.degIn S v = 2) {x : D} (hx : M.atom x = v) : M.atom (M.mate x) ≠ v := by
  classical
  intro hloop
  let T := (M.dartsAt v).filter (M.InGroup S)
  have hsub : {x,M.mate x} ⊆ T := by
    intro y hy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hy
    apply Finset.mem_filter.mpr
    rcases hy with rfl | rfl
    · exact ⟨(mem_dartsAt M v _).mpr hx,hx.symm ▸ hv,hloop.symm ▸ hv⟩
    · exact ⟨(mem_dartsAt M v (M.mate x)).mpr hloop,hloop.symm ▸ hv,
        by rw [M.mate_mate,hx]; exact hv⟩
  have he : {x,M.mate x} = T := by
    apply Finset.eq_of_subset_of_card_le hsub
    change M.degIn S v ≤ ({x,M.mate x}:Finset D).card
    rw [hd,Finset.card_pair (Ne.symm (M.mate_ne x))]
  have hproper : ¬ S ⊆ {v} := by
    intro hh
    exact hne (Finset.mem_singleton.mp (hh hz))
  obtain ⟨u,hu,y,hy,hyout,hadj⟩ := connected_group_boundary M
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v) hproper hc.2
  have huv := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨e,hev,hey⟩ := hadj
  have hem : e ∈ T := Finset.mem_filter.mpr
    ⟨(mem_dartsAt M v e).mpr hev,hev.symm ▸ hv,hey.symm ▸ hy⟩
  rw [← he] at hem
  simp only [Finset.mem_insert,Finset.mem_singleton] at hem
  have hyv : y = v := by
    rcases hem with rfl | rfl
    · exact hey.symm.trans hloop
    · exact hey.symm.trans (by rw [M.mate_mate]; exact hx)
  exact hyout (Finset.mem_singleton.mpr hyv)

/-- In a connected block, neither joint can carry a self-loop. -/
theorem connected_block_no_joint_loop {S : Finset V} {j1 j2 : V}
    (hB : M.IsBlock S j1 j2) (hc : GroupConnected M S) {x : D}
    (hx : M.atom x = j1 ∨ M.atom x = j2) : M.atom (M.mate x) ≠ M.atom x := by
  obtain ⟨h1,h2⟩ := block_joint_degrees M hB
  have hne := hB.2.2.2.1
  rcases hx with hx | hx
  · rw [hx]
    exact connected_degree_two_no_loop M hc hB.2.1 hB.2.2.1 (Ne.symm hne) h1 hx
  · rw [hx]
    exact connected_degree_two_no_loop M hc hB.2.2.1 hB.2.1 hne h2 hx

end WaveTurbulence.Mole
