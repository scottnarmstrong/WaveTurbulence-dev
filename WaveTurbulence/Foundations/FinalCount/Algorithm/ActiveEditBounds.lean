/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ActivePotential
public import WaveTurbulence.Foundations.FinalCount.Algorithm.NewLinkBounds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.DegreeCountBounds
public import WaveTurbulence.Foundations.FinalCount.AppBBridgeMolecule
import Mathlib.Tactic

/-! # Bounded decrease of the active potential under actual graph edits -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem deletion_activePotential_drop_le {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) :
    activeLinkPotential M-((P.removed.card : ℤ)+P.vertices.card) ≤ activeLinkPotential r.post := by
  have hv := r.post_card_atoms
  have hlink : (appbLinks r.post).card ≤ (appbLinks M).card := by
    change (appbLinks (Degen.eraseAtoms M r.removedAtoms)).card ≤ _
    rw [appbLinks_eraseAtoms]
    exact card_filter_le _ _
  have hi := (abs_le.mp (deletion_degreeCount_change_abs_le r 0)).2
  unfold activeLinkPotential linkPotential
  omega

theorem insertion_activePotential_drop_le (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hN : (addBond M a b).IsMolecule) :
    activeLinkPotential M-8 ≤ activeLinkPotential (addBond M a b) := by
  classical
  have hatoms : (addBond M a b).atoms = M.atoms := by
    change insert a (insert b M.atoms) = _
    simp only [insert_eq_of_mem ha,insert_eq_of_mem hb]
  have hi : (appbDegreeAtoms (addBond M a b) 0).card ≤ (appbDegreeAtoms M 0).card := by
    apply card_le_card
    intro v hv
    obtain ⟨hv,hd⟩ := mem_filter.mp hv
    have hvM := hatoms ▸ hv
    have hh := addBond_deg M a b v
    have hdM : M.deg v = 0 := by omega
    exact mem_filter.mpr ⟨hvM,hdM⟩
  have hl := addBond_links_card_le M a b hN
  unfold activeLinkPotential linkPotential
  rw [hatoms]
  omega

theorem bond_removal_activePotential_drop_le (M : Molecule V D) (hM : M.IsMolecule) (e : D) :
    activeLinkPotential M-10 ≤ activeLinkPotential (eraseBond M e) := by
  classical
  let S : Finset V := {M.atom e,M.atom (M.mate e)}
  have hS : S ⊆ M.atoms := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact M.atom_mem _
    · exact (mem_singleton.mp hv) ▸ M.atom_mem _
  have hdeg : ∀ v ∈ M.atoms,v ∉ S → (eraseBond M e).deg v = M.deg v := by
    intro v hv hn
    have ha : M.atom e ≠ v := fun he => hn (he ▸ mem_insert_self _ _)
    have hb : M.atom (M.mate e) ≠ v := fun he => hn (he ▸ mem_insert_of_mem (mem_singleton_self _))
    have hh := appb_eraseBond_degree M e v
    simpa only [ha,hb,ite_false,add_zero] using hh
  have hi := (abs_le.mp (same_atoms_degreeCount_change_abs_le M (eraseBond M e) rfl S hS hdeg 0)).2
  have hc : S.card ≤ 2 := card_le_two
  have hl := eraseBond_links_card_le M e (appb_eraseBond_isMolecule M hM e)
  unfold activeLinkPotential linkPotential
  have hatoms : (eraseBond M e).atoms = M.atoms := rfl
  rw [hatoms]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
