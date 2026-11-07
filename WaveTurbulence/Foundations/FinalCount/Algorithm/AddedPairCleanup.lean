/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TripleCleanupInvariant
import Mathlib.Tactic

/-! # At most one actual TB cleanup after inserting a defective pair -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A single insertion into a no-triple graph either needs no cleanup or
has a concrete TB-1/2 realization whose deletion restores no-triple.
The excluded degree-four pair is precisely the source eligibility test. -/
theorem addedPair_cleanup (M : Molecule V D) (h : AppbNoTripleBonds M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hne : a ≠ b)
    (hM : (addBond M a b).IsMolecule) (hno : AppbNoLoops (addBond M a b))
    (hd : (addBond M a b).bondsBetween a b = 3 →
      ¬((addBond M a b).deg a = 4 ∧ (addBond M a b).deg b = 4)) :
    AppbNoTripleBonds (addBond M a b) ∨
      ∃ k ∈ ([AppbPatternKind.tb1,.tb2] : List _),
        ∃ r : AppbRealization (addBond M a b) k.pattern,
          a ∈ r.removedAtoms ∧ b ∈ r.removedAtoms ∧ AppbNoTripleBonds r.post := by
  classical
  have hatoms : (addBond M a b).atoms = M.atoms := by
    change insert a (insert b M.atoms) = M.atoms
    simp only [insert_eq_of_mem hb,insert_eq_of_mem ha]
  by_cases hc : (addBond M a b).bondsBetween a b ≤ 2
  · left
    intro u hu v hv huv
    by_contra hn
    have hp := large_multiplicity_addBond_endpoints M h a b (hatoms ▸ hu) (hatoms ▸ hv) huv (lt_of_not_ge hn)
    have he : (addBond M a b).bondsBetween u v = (addBond M a b).bondsBetween a b := by
      rcases Sym2.eq_iff.mp hp with hp | hp
      · rw [hp.1,hp.2]
      · rw [hp.1,hp.2]
        exact bondsBetween_symm _ _ _
    exact hn (he ▸ hc)
  · right
    have hm : (addBond M a b).bondsBetween a b = 3 := by
      have he := appb_addBond_bondsBetween M a b a b
      rw [if_pos rfl] at he
      have hh := h a ha b hb hne
      omega
    obtain ⟨k,hk,r,haY,hbY⟩ := exists_triple_deletion_cover (addBond M a b) hM hno
      (hatoms.symm ▸ ha) (hatoms.symm ▸ hb) hne hm (hd hm)
    exact ⟨k,hk,r,haY,hbY,noTriple_after_added_pair_cleanup M h ha hb r haY⟩

end WaveTurbulence.Mole.AppbAlgorithm
