/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideBonds
public import WaveTurbulence.Foundations.FinalCount.Algorithm.ClosedSideComponents
public import WaveTurbulence.Foundations.FinalCount.AppBBranchConditions
import Mathlib.Tactic

/-! # Actual component sides satisfy the original molecule axioms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem degree_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a : V} (ha : a ∈ S) : (appbSideMolecule M S hS).deg a = M.deg a := by
  simpa [Molecule.deg] using appb_sum_dartsAt_side M S hS (fun _ => (1 : ℕ)) ha

theorem oriented_degree_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    {a : V} (ha : a ∈ S) (t : Bool) :
    (((appbSideMolecule M S hS).dartsAt a).filter (fun x => (appbSideMolecule M S hS).out x = t)).card =
      ((M.dartsAt a).filter (fun x => M.out x = t)).card := by
  apply card_bij (fun x _ => x.val)
  · intro x hx
    obtain ⟨hx,ho⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,ho⟩
  · intro x hx y hy he
    exact Subtype.ext he
  · intro x hx
    obtain ⟨hx,ho⟩ := mem_filter.mp hx
    have hax := (mem_filter.mp hx).2
    refine ⟨⟨x,hax.symm ▸ ha⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hax⟩,ho⟩

/-- Nonsaturation is inherited because a closed side contains the whole
old component of each of its atoms, including its actual defect atom. -/
theorem isMolecule_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (hM : M.IsMolecule) : (appbSideMolecule M S hS).IsMolecule := by
  constructor
  · intro a ha
    have hh := hM.1 a (hS.subset_atoms ha)
    change (((appbSideMolecule M S hS).dartsAt a).filter (fun x => (appbSideMolecule M S hS).out x = true)).card ≤ 2 ∧
      (((appbSideMolecule M S hS).dartsAt a).filter (fun x => (appbSideMolecule M S hS).out x = false)).card ≤ 2
    rw [oriented_degree_closed_side M S hS ha true,oriented_degree_closed_side M S hS ha false]
    exact hh
  · intro a ha
    obtain ⟨b,hb,hp,hd⟩ := hM.2 a (hS.subset_atoms ha)
    have hbS := (hS.path_mem_iff hp).mp ha
    exact ⟨b,hbS,old_path_to_closed_side M S hS hp ha,
      (degree_closed_side M S hS hbS).trans_ne hd⟩

theorem noLoops_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (h : AppbNoLoops M) : AppbNoLoops (appbSideMolecule M S hS) := fun x => h x.val

theorem noTripleBonds_closed_side (M : Molecule V D) (S : Finset V) (hS : AppbClosedSide M S)
    (h : AppbNoTripleBonds M) : AppbNoTripleBonds (appbSideMolecule M S hS) := by
  intro a ha b hb hab
  rw [bondsBetween_closed_side M S hS ha hb]
  exact h a (hS.subset_atoms ha) b (hS.subset_atoms hb) hab

theorem component_side_connected (M : Molecule V D) (a : V) :
    ∀ u ∈ (appbSideMolecule M (componentSet M a) (appb_componentSet_closed M a)).atoms,
    ∀ v ∈ (appbSideMolecule M (componentSet M a) (appb_componentSet_closed M a)).atoms,
      (appbSideMolecule M (componentSet M a) (appb_componentSet_closed M a)).SameComponent u v := by
  intro u hu v hv
  have hp := Relation.EqvGen.trans _ _ _ ((mem_componentSet M a u).mp hu).2.symm
    ((mem_componentSet M a v).mp hv).2
  exact old_path_to_closed_side M _ (appb_componentSet_closed M a) hp hu

end WaveTurbulence.Mole.AppbAlgorithm
