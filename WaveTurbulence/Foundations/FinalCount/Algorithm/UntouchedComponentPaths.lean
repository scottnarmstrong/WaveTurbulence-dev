/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.GeneralCircuitDeletion
import Mathlib.Tactic

/-! # Untouched components survive a connected finite deletion literally -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open Finset
open WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem erase_path_of_untouched_component (M : Molecule V D) (Y : Finset V) (v : V)
    (hY : ∀ y ∈ Y,M.SameComponent y v) {a b : V} (hp : M.SameComponent a b) :
    ¬M.SameComponent a v → (eraseAtoms M Y).SameComponent a b := by
  induction hp with
  | rel a b hab =>
    intro hn
    apply (eraseAtoms_sameComponent_iff M Y a b).mpr
    apply Relation.EqvGen.rel
    refine ⟨?_,?_,hab⟩
    · exact fun ha => hn (hY a ha)
    · exact fun hb => hn (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ hab) (hY b hb))
  | refl a => intro hn; exact Relation.EqvGen.refl _
  | symm a b hab ih =>
    intro hn
    exact (ih (fun hbv => hn (Relation.EqvGen.trans _ _ _ hab.symm hbv))).symm
  | trans a b c hab hp ih ih' =>
    intro hn
    exact Relation.EqvGen.trans _ _ _ (ih hn)
      (ih' (fun hbv => hn (Relation.EqvGen.trans _ _ _ hab hbv)))

theorem componentSet_erase_untouched (M : Molecule V D) (Y : Finset V) (v : V)
    (hY : ∀ y ∈ Y,M.SameComponent y v) {a : V} (hn : ¬M.SameComponent a v) :
    componentSet (eraseAtoms M Y) a = componentSet M a := by
  ext b
  simp only [mem_componentSet]
  constructor
  · rintro ⟨hb,hp⟩
    exact ⟨(mem_sdiff.mp hb).1,MoleProp.sameComponent_of_erase M Y hp⟩
  · rintro ⟨hb,hp⟩
    have hbY : b ∉ Y := fun hy => hn (Relation.EqvGen.trans _ _ _ hp (hY b hy))
    exact ⟨mem_sdiff.mpr ⟨hb,hbY⟩,erase_path_of_untouched_component M Y v hY hp hn⟩

theorem residual_component_mem_new_of_path_to_removed (M : Molecule V D) (Y : Finset V)
    {v a : V} (hv : v ∈ Y) (ha : a ∈ M.atoms \ Y) (hp : M.SameComponent a v) :
    residualComponent M Y a ∈ newComponents M Y := by
  classical
  have href : a ∈ residualComponent M Y a :=
    (mem_residualComponent M Y a a).mpr ⟨(mem_sdiff.mp ha).1,(mem_sdiff.mp ha).2,Relation.EqvGen.refl _⟩
  have hboundary : (boundaryDarts M (residualComponent M Y a)).Nonempty := by
    by_contra hn
    have he := not_nonempty_iff_eq_empty.mp hn
    have hv' := (sameComponent_mem_iff_of_boundary_empty M _ he hp).mp href
    exact ((mem_residualComponent M Y a v).mp hv').2.1 hv
  exact mem_filter.mpr ⟨mem_image.mpr ⟨a,ha,rfl⟩,hboundary⟩

end WaveTurbulence.Mole.AppbAlgorithm
