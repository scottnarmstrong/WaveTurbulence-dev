/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSide
public import WaveTurbulence.Foundations.FinalCount.AppBTwoComponentPaths
import Mathlib.Tactic

/-! # Actual connected components as closed induced groups -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem AppbClosedSide.path_mem_iff {M : Molecule V D} {S : Finset V}
    (h : AppbClosedSide M S) {a b : V} (hp : M.SameComponent a b) : a ∈ S ↔ b ∈ S := by
  induction hp with
  | rel u v hrel =>
    obtain ⟨x,hx,hy⟩ := hrel
    rw [← hx,← hy]
    exact h.mate_mem x
  | refl u => rfl
  | symm u v hp ih => exact ih.symm
  | trans u v w hp hp' ih ih' => exact ih.trans ih'

theorem AppbClosedSide.induced_path {M : Molecule V D} {S : Finset V}
    (h : AppbClosedSide M S) {a b : V} (hp : M.SameComponent a b) (ha : a ∈ S) :
    (induced M S).SameComponent a b := by
  induction hp with
  | rel u v hrel =>
    have hb := (h.path_mem_iff (Relation.EqvGen.rel _ _ hrel)).mp ha
    exact Relation.EqvGen.rel _ _ ((induced_adj_iff M S u v).mpr ⟨hrel,ha,hb⟩)
  | refl u => exact Relation.EqvGen.refl _
  | symm u v hp ih => exact (ih ((h.path_mem_iff hp).mpr ha)).symm
  | trans u v w hp hp' ih ih' =>
    exact Relation.EqvGen.trans _ _ _ (ih ha) (ih' ((h.path_mem_iff hp).mp ha))

theorem appb_componentSet_closed (M : Molecule V D) (a : V) :
    AppbClosedSide M (Degen.componentSet M a) where
  subset_atoms := by intro u hu; exact ((Degen.mem_componentSet M a u).mp hu).1
  mate_mem := by
    intro x
    simp only [Degen.mem_componentSet,M.atom_mem,true_and]
    have hp : M.SameComponent (M.atom x) (M.atom (M.mate x)) := Relation.EqvGen.rel _ _ ⟨x,rfl,rfl⟩
    exact ⟨fun h => Relation.EqvGen.trans _ _ _ h hp,
      fun h => Relation.EqvGen.trans _ _ _ h hp.symm⟩

theorem appb_componentSet_groupConnected (M : Molecule V D) {a : V} (ha : a ∈ M.atoms) :
    GroupConnected M (Degen.componentSet M a) := by
  refine ⟨⟨a,(Degen.mem_componentSet M a a).mpr ⟨ha,Relation.EqvGen.refl _⟩⟩,?_⟩
  intro u hu v hv
  have hp := Relation.EqvGen.trans _ _ _ ((Degen.mem_componentSet M a u).mp hu).2.symm
    ((Degen.mem_componentSet M a v).mp hv).2
  exact (appb_componentSet_closed M a).induced_path hp hu

end WaveTurbulence.Mole
