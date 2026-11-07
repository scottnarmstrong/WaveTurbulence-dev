/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TripleDeletionCover
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondPairs
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionMolecule
import Mathlib.Tactic

/-! # One endpoint-covering cleanup restores the no-triple invariant -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Adding one bond can create excessive multiplicity only at its own
endpoint pair, including arbitrary old cross-component constraints. -/
theorem large_multiplicity_addBond_endpoints (M : Molecule V D) (h : AppbNoTripleBonds M)
    (a b : V) {u v : V} (hu : u ∈ M.atoms) (hv : v ∈ M.atoms) (hne : u ≠ v)
    (hm : 2 < (addBond M a b).bondsBetween u v) : s(u,v) = s(a,b) := by
  by_contra hn
  have he := appb_addBond_bondsBetween M a b u v
  rw [if_neg (Ne.symm hn),add_zero] at he
  have hb := h u hu v hv hne
  omega

/-- Literal deletion of either offending endpoint removes every possible
large-multiplicity pair. No no-triple conclusion is a premise. -/
theorem noTriple_eraseAtoms_of_only_pair (M : Molecule V D) (Y : Finset V) (a b : V)
    (ha : a ∈ Y)
    (hpair : ∀ u ∈ M.atoms,∀ v ∈ M.atoms,u ≠ v → 2 < M.bondsBetween u v → s(u,v) = s(a,b)) :
    AppbNoTripleBonds (Degen.eraseAtoms M Y) := by
  intro u hu v hv hne
  have hu' := mem_sdiff.mp hu
  have hv' := mem_sdiff.mp hv
  have he := Degen.bondsBetween_erase_eq M Y hu'.2 hv'.2
  rw [he]
  by_contra hn
  have hp := hpair u hu'.1 v hv'.1 hne (lt_of_not_ge hn)
  rcases Sym2.eq_iff.mp hp with h | h
  · exact hu'.2 (h.1.symm ▸ ha)
  · exact hv'.2 (h.2.symm ▸ ha)

/-- After one insertion into an old no-triple molecule, any actual TB
realization covering its endpoints restores no-triple immediately. -/
theorem noTriple_after_added_pair_cleanup (M : Molecule V D) (h : AppbNoTripleBonds M)
    {a b : V} (ha : a ∈ M.atoms) (hb : b ∈ M.atoms)
    {P : AppbPattern} (r : AppbRealization (addBond M a b) P) (haY : a ∈ r.removedAtoms) :
    AppbNoTripleBonds r.post := by
  apply noTriple_eraseAtoms_of_only_pair (addBond M a b) r.removedAtoms a b haY
  have hatoms : (addBond M a b).atoms = M.atoms := by
    change insert a (insert b M.atoms) = M.atoms
    simp only [insert_eq_of_mem hb,insert_eq_of_mem ha]
  intro u hu v hv hne hm
  exact large_multiplicity_addBond_endpoints M h a b (hatoms ▸ hu) (hatoms ▸ hv) hne hm

end WaveTurbulence.Mole.AppbAlgorithm
