/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.UntouchedComponentPaths
import Mathlib.Tactic

/-! # Exact global component change for a connected finite deletion -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem componentSets_erase_connected (M : Molecule V D) (Y : Finset V) {v : V}
    (hv : v ∈ Y) (hvM : v ∈ M.atoms) (hY : ∀ y ∈ Y,M.SameComponent y v) :
    componentSets (eraseAtoms M Y) = (componentSets M).erase (componentSet M v) ∪ newComponents M Y := by
  classical
  ext S
  constructor
  · intro hS
    change S ∈ (M.atoms \ Y).image (componentSet (eraseAtoms M Y)) at hS
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
    have haM := (mem_sdiff.mp ha).1
    by_cases hp : M.SameComponent a v
    · apply mem_union_right
      rw [eraseAtoms_componentSet]
      exact residual_component_mem_new_of_path_to_removed M Y hv ha hp
    · apply mem_union_left
      rw [componentSet_erase_untouched M Y v hY hp]
      exact mem_erase.mpr ⟨fun he => hp ((componentSet_eq_iff M haM).mp he),
        mem_image.mpr ⟨a,haM,rfl⟩⟩
  · intro hS
    rcases mem_union.mp hS with hS | hS
    · obtain ⟨hne,hS⟩ := mem_erase.mp hS
      change S ∈ M.atoms.image (componentSet M) at hS
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
      have hn : ¬M.SameComponent a v := fun hp => hne ((componentSet_eq_iff M ha).mpr hp)
      have haY : a ∉ Y := fun hy => hn (hY a hy)
      change componentSet M a ∈ (M.atoms \ Y).image (componentSet (eraseAtoms M Y))
      exact mem_image.mpr ⟨a,mem_sdiff.mpr ⟨ha,haY⟩,componentSet_erase_untouched M Y v hY hn⟩
    · exact MoleProp.newComponents_subset_componentSets_erase M Y hS

theorem untouched_components_disjoint_new_connected (M : Molecule V D) (Y : Finset V) (v : V) :
    Disjoint ((componentSets M).erase (componentSet M v)) (newComponents M Y) := by
  classical
  apply disjoint_left.mpr
  intro S hOld hNew
  have hS := (mem_erase.mp hOld).2
  change S ∈ M.atoms.image (componentSet M) at hS
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hS
  have hboundary := (mem_filter.mp hNew).2
  rw [MoleProp.boundary_componentSet_eq_empty] at hboundary
  exact not_nonempty_empty hboundary

/-- The deleted atoms lie in one old component. Its old quotient class is
replaced by the actual newly bounded residual components; all other old
classes survive. No component-count formula is a premise. -/
theorem numComponents_erase_connected_add_one (M : Molecule V D) (Y : Finset V) {v : V}
    (hv : v ∈ Y) (hvM : v ∈ M.atoms) (hY : ∀ y ∈ Y,M.SameComponent y v) :
    (eraseAtoms M Y).numComponents+1 = M.numComponents+(newComponents M Y).card := by
  classical
  have hm : componentSet M v ∈ componentSets M := mem_image.mpr ⟨v,hvM,rfl⟩
  have he := card_erase_add_one hm
  rw [numComponents_eq_card_componentSets,numComponents_eq_card_componentSets,
    componentSets_erase_connected M Y hv hvM hY,
    card_union_of_disjoint (untouched_components_disjoint_new_connected M Y v)]
  omega

end WaveTurbulence.Mole.AppbAlgorithm
