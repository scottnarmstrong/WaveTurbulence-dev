/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.LowDegreeConnectivity
public import WaveTurbulence.Foundations.FinalCount.Degen.CircuitDeletion
import Mathlib.Tactic

/-! # Exact circuit change for deletion in disconnected molecules

DH23 Proposition 10.1 repeatedly deletes atoms after disconnection. The
actual old component containing the deleted atom is replaced by the new
boundary components; all other actual components survive unchanged.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Residual paths are actual old paths. -/
theorem sameComponent_of_erase (M : Molecule V D) (Y : Finset V) {u w : V}
    (h : (eraseAtoms M Y).SameComponent u w) : M.SameComponent u w := by
  have hp := (eraseAtoms_sameComponent_iff M Y u w).mp h
  clear h
  induction hp with
  | rel a b hab => exact Relation.EqvGen.rel _ _ hab.2.2
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

/-- A path in a component not containing v survives removal of v. -/
theorem sameComponent_erase_of_not_sameComponent (M : Molecule V D) {u w v : V}
    (hp : M.SameComponent u w) :
    ¬M.SameComponent u v → (eraseAtoms M {v}).SameComponent u w := by
  induction hp with
  | rel a b hab =>
    intro hn
    apply (eraseAtoms_sameComponent_iff M {v} a b).mpr
    apply Relation.EqvGen.rel
    refine ⟨?_,?_,hab⟩
    · simpa only [mem_singleton] using (fun he : a = v => hn (he ▸ Relation.EqvGen.refl a))
    · simpa only [mem_singleton] using
        (fun he : b = v => hn (he ▸ Relation.EqvGen.rel a b hab))
  | refl a => intro _; exact Relation.EqvGen.refl a
  | symm a b hab ih =>
    intro hn
    apply Relation.EqvGen.symm
    apply ih
    intro hav
    exact hn (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hab) hav)
  | trans a b c hab _ ih ih' =>
    intro hn
    exact Relation.EqvGen.trans _ _ _ (ih hn)
      (ih' (fun hbv => hn (Relation.EqvGen.trans _ _ _ hab hbv)))

/-- An entire old component has empty boundary in the old molecule. -/
theorem boundary_componentSet_eq_empty (M : Molecule V D) (u : V) :
    boundaryDarts M (componentSet M u) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hx,hnot⟩ := (mem_filter.mp hx).2
  have hp := ((mem_componentSet M u (M.atom x)).mp hx).2
  apply hnot
  apply (mem_componentSet M u (M.atom (M.mate x))).mpr
  exact ⟨M.atom_mem _,Relation.EqvGen.trans _ _ _ hp
    (Relation.EqvGen.rel _ _ ⟨x,rfl,rfl⟩)⟩

/-- The component set of an untouched component is literally unchanged. -/
theorem componentSet_erase_of_not_sameComponent (M : Molecule V D) {u v : V}
    (hn : ¬M.SameComponent u v) :
    componentSet (eraseAtoms M {v}) u = componentSet M u := by
  ext w
  simp only [mem_componentSet]
  constructor
  · rintro ⟨hw,hp⟩
    exact ⟨(mem_sdiff.mp hw).1,sameComponent_of_erase M {v} hp⟩
  · rintro ⟨hw,hp⟩
    have hwv : w ≠ v := fun he => hn (he ▸ hp)
    exact ⟨mem_sdiff.mpr ⟨hw,by simpa only [mem_singleton] using hwv⟩,
      sameComponent_erase_of_not_sameComponent M hp hn⟩

/-- Every actual newly bounded residual component is an actual component
of the erased molecule, even without global old connectedness. -/
theorem newComponents_subset_componentSets_erase (M : Molecule V D) (Y : Finset V) :
    newComponents M Y ⊆ componentSets (eraseAtoms M Y) := by
  classical
  intro S hS
  obtain ⟨hS,_⟩ := mem_filter.mp hS
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
  unfold componentSets
  apply mem_image.mpr
  exact ⟨u,hu,eraseAtoms_componentSet M Y u⟩

/-- Exact family decomposition: untouched old components and the new
components replacing the one containing the removed atom. -/
theorem componentSets_erase_singleton (M : Molecule V D) {v : V} (hv : v ∈ M.atoms) :
    componentSets (eraseAtoms M {v}) =
      (componentSets M).erase (componentSet M v) ∪ newComponents M {v} := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
    have huold : u ∈ M.atoms := (mem_sdiff.mp hu).1
    have huv : u ≠ v := by simpa only [mem_singleton] using (mem_sdiff.mp hu).2
    by_cases hp : M.SameComponent u v
    · apply mem_union_right
      rw [eraseAtoms_componentSet]
      exact residualComponent_mem_newComponents_of_sameComponent M hv huold huv hp
    · apply mem_union_left
      rw [componentSet_erase_of_not_sameComponent M hp]
      apply mem_erase.mpr
      exact ⟨fun he => hp ((componentSet_eq_iff M huold).mp he),mem_image.mpr ⟨u,huold,rfl⟩⟩
  · intro hS
    rcases mem_union.mp hS with hS | hS
    · obtain ⟨hne,hS⟩ := mem_erase.mp hS
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hS
      have hn : ¬M.SameComponent u v := fun hp => hne ((componentSet_eq_iff M hu).mpr hp)
      have huv : u ≠ v := fun he => hn (he ▸ Relation.EqvGen.refl u)
      unfold componentSets
      apply mem_image.mpr
      refine ⟨u,mem_sdiff.mpr ⟨hu,?_⟩,componentSet_erase_of_not_sameComponent M hn⟩
      simpa only [mem_singleton] using huv
    · exact newComponents_subset_componentSets_erase M {v} hS

/-- No untouched old component is a newly bounded component. -/
theorem untouched_components_disjoint_new (M : Molecule V D) (v : V) :
    Disjoint ((componentSets M).erase (componentSet M v)) (newComponents M {v}) := by
  classical
  apply disjoint_left.mpr
  intro S hOld hNew
  obtain ⟨u,_hu,rfl⟩ := mem_image.mp (mem_erase.mp hOld).2
  have hb := (mem_filter.mp hNew).2
  rw [boundary_componentSet_eq_empty] at hb
  exact Finset.not_nonempty_empty hb

/-- Exact actual quotient count for arbitrary disconnected old graphs.
The +1 formulation avoids subtraction on natural component counts. -/
theorem numComponents_erase_singleton_add_one (M : Molecule V D)
    {v : V} (hv : v ∈ M.atoms) :
    (eraseAtoms M {v}).numComponents + 1 = M.numComponents + (newComponents M {v}).card := by
  classical
  have hmem : componentSet M v ∈ componentSets M := mem_image.mpr ⟨v,hv,rfl⟩
  have he := card_erase_add_one hmem
  rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets,
    componentSets_erase_singleton M hv,card_union_of_disjoint (untouched_components_disjoint_new M v)]
  omega

/-- DH23 Proposition 10.1: the exact circuit change of a single atom
removal, valid also after earlier operations disconnected the graph. -/
theorem circuitRank_erase_singleton_sub_general (M : Molecule V D)
    {v : V} (hv : v ∈ M.atoms) :
    (eraseAtoms M {v}).circuitRank - M.circuitRank =
      ((newComponents M {v}).card : ℤ) - (incidentBondsAt M v).card := by
  have hE := card_bonds_erase_singleton_add_incident M v
  have hV := card_atoms_erase_singleton_add_one M hv
  have hF := numComponents_erase_singleton_add_one M hv
  unfold Molecule.circuitRank
  omega

/-- Actual vertex deletion never increases circuit rank, with no global
connectedness assumption and with self-loops counted correctly. -/
theorem circuitRank_erase_singleton_le_general (M : Molecule V D)
    {v : V} (hv : v ∈ M.atoms) :
    (eraseAtoms M {v}).circuitRank ≤ M.circuitRank := by
  have hc := card_newComponents_le_boundary M {v}
  have hb := card_boundary_add_twice_self_eq_deg M v
  have hi := card_incident_add_self_eq_deg M v
  have hdrop := circuitRank_erase_singleton_sub_general M hv
  omega

end WaveTurbulence.MoleProp
