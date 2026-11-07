/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CoreGeometry
public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103CutConnectivity
import Mathlib.Tactic

/-! # Selecting an actual nontrivial bridge-core component -/

@[expose] public section
set_option autoImplicit false
open Finset
open WaveTurbulence.Degen
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Restricting to an entire component keeps every incident dart. -/
theorem induced_component_degree (M : Molecule V D) (v : V) {a : V}
    (ha : a ∈ componentSet M v) : (Mole.induced M (componentSet M v)).deg a = M.deg a := by
  rw [Mole.induced_deg]
  have he : (M.dartsAt a).filter (M.InGroup (componentSet M v)) = M.dartsAt a := by
    apply filter_eq_self.mpr
    intro x hx
    have hxa := (Mole.mem_dartsAt M a x).mp hx
    refine ⟨hxa.symm ▸ ha,?_⟩
    apply (mem_componentSet _ _ _).mpr
    exact ⟨M.atom_mem _,Relation.EqvGen.trans _ _ _ ((mem_componentSet _ _ _).mp ha).2
      (Relation.EqvGen.rel _ _ ⟨x,hxa,rfl⟩)⟩
  exact congrArg Finset.card he

/-- The selected active core component has degrees three/four everywhere;
no zero-degree vertex is smuggled into the next source search state. -/
theorem selected_core_min_degree (M : Molecule V D)
    (hp : ∀ a ∈ M.atoms, (bridgeCore M).deg a = 0 ∨
      (bridgeCore M).deg a = 3 ∨ (bridgeCore M).deg a = 4)
    {v : V} (hv3 : (bridgeCore M).deg v = 3) :
    ∀ a ∈ componentSet (bridgeCore M) v,
      (Mole.induced (bridgeCore M) (componentSet (bridgeCore M) v)).deg a = 3 ∨
      (Mole.induced (bridgeCore M) (componentSet (bridgeCore M) v)).deg a = 4 := by
  intro a ha
  rw [induced_component_degree _ _ ha]
  rcases hp a ((mem_componentSet _ _ _).mp ha).1 with hz | h3 | h4
  · have heq := sameComponent_eq_of_degree_zero (bridgeCore M) hz
      (Relation.EqvGen.symm _ _ ((mem_componentSet _ _ _).mp ha).2)
    have hh := hv3
    rw [heq,hz] at hh
    omega
  · exact Or.inl h3
  · exact Or.inr h4

/-- A literal selected core component is connected in its actual induced
carrier. -/
theorem selected_core_connected (M : Molecule V D) (v : V) :
    ∀ a ∈ componentSet (bridgeCore M) v, ∀ b ∈ componentSet (bridgeCore M) v,
      (Mole.induced (bridgeCore M) (componentSet (bridgeCore M) v)).SameComponent a b := by
  intro a ha b hb
  apply sameComponent_induced_of_boundary_empty _ _
    (boundary_componentSet_eq_empty (bridgeCore M) v) ha
  exact Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ ((mem_componentSet _ _ _).mp ha).2)
    ((mem_componentSet _ _ _).mp hb).2

/-- Restricting to an induced atomic group decreases oriented stars. -/
theorem card_filtered_dartsAt_induced_le (M : Molecule V D) (U : Finset V) (v : V)
    (p : D → Prop) [DecidablePred p] :
    (((Mole.induced M U).dartsAt v).filter (fun z => p z.val)).card ≤ ((M.dartsAt v).filter p).card := by
  classical
  have hs : ((((Mole.induced M U).dartsAt v).filter (fun z => p z.val)).image
      (fun z => z.val)) ⊆ (M.dartsAt v).filter p := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have hh := mem_filter.mp hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v x.val).mpr
      ((Mole.mem_dartsAt _ v x).mp hh.1),hh.2⟩
  have hc := card_le_card hs
  rw [card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

/-- Selecting a whole actual component preserves the molecule axioms. -/
theorem induced_component_isMolecule (M : Molecule V D) (hM : M.IsMolecule) (v : V) :
    (Mole.induced M (componentSet M v)).IsMolecule := by
  classical
  let C := componentSet M v
  constructor
  · intro z hz
    have hzM := ((mem_componentSet M v z).mp hz).1
    exact ⟨(card_filtered_dartsAt_induced_le M C z (fun x => M.out x = true)).trans (hM.1 z hzM).1,
      (card_filtered_dartsAt_induced_le M C z (fun x => M.out x = false)).trans (hM.1 z hzM).2⟩
  · intro z hz
    obtain ⟨a,ha,hza,hne⟩ := hM.2 z ((mem_componentSet M v z).mp hz).1
    have haC : a ∈ C := (mem_componentSet M v a).mpr ⟨ha,Relation.EqvGen.trans _ _ _
      ((mem_componentSet M v z).mp hz).2 hza⟩
    refine ⟨a,haC,sameComponent_induced_of_boundary_empty M C
      (boundary_componentSet_eq_empty M v) hz hza,?_⟩
    rw [induced_component_degree M v haC]
    exact hne

/-- Old boundaries of subsets of one whole component are exactly the
actual induced boundaries, with only their dart subtype forgotten. -/
theorem boundary_eq_image_induced_component (M : Molecule V D) (v : V) (U : Finset V)
    (hU : U ⊆ componentSet M v) : boundaryDarts M U =
      (boundaryDarts (Mole.induced M (componentSet M v)) U).image (fun z => z.val) := by
  classical
  ext z
  constructor
  · intro hz
    have hh := (mem_filter.mp hz).2
    have hzC := hU hh.1
    have hmC : M.atom (M.mate z) ∈ componentSet M v := (mem_componentSet M v _).mpr
      ⟨M.atom_mem _,Relation.EqvGen.trans _ _ _ ((mem_componentSet M v _).mp hzC).2
        (Relation.EqvGen.rel _ _ ⟨z,rfl,rfl⟩)⟩
    exact mem_image.mpr ⟨⟨z,hzC,hmC⟩,mem_filter.mpr ⟨mem_univ _,hh⟩,rfl⟩
  · intro hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩

/-- No bridge can be created by selecting an entire actual component. -/
theorem induced_component_bridgeless (M : Molecule V D) (hbridge : ∀ e, ¬ IsBridge M e) (v : V) :
    ∀ e, ¬ IsBridge (Mole.induced M (componentSet M v)) e := by
  intro e he
  let N := Mole.induced M (componentSet M v)
  have hb := boundary_bridgeSide N e he
  have hold := boundary_eq_image_induced_component M v (bridgeSide N e) (bridgeSide_subset N e)
  rw [hb,image_singleton] at hold
  exact hbridge e.val (isBridge_of_single_boundary M _ hold)

/-- Simplicity of the old graph is inherited by every actual induced group. -/
theorem induced_simple (M : Molecule V D) (U : Finset V)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ∀ a b, a ≠ b → (Mole.induced M U).bondsBetween a b ≤ 1 := by
  intro a b hab
  rw [← card_neighborDarts _ hab]
  have hcard : (neighborDarts M a b).card ≤ 1 := by
    rw [card_neighborDarts M hab]
    exact hsimple a b hab
  apply card_le_one.mpr
  intro x hx y hy
  apply Subtype.ext
  apply card_le_one.mp hcard
  · have hh := mem_filter.mp hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a x.val).mpr ((Mole.mem_dartsAt _ a x).mp hh.1),hh.2⟩
  · have hh := mem_filter.mp hy
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a y.val).mpr ((Mole.mem_dartsAt _ a y).mp hh.1),hh.2⟩

/-- Bridge pruning only removes bonds, so old simplicity survives. -/
theorem bridgeCore_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ∀ a b, a ≠ b → (bridgeCore M).bondsBetween a b ≤ 1 := by
  intro a b hab
  rw [← card_neighborDarts _ hab]
  have hcard : (neighborDarts M a b).card ≤ 1 := by
    rw [card_neighborDarts M hab]
    exact hsimple a b hab
  apply card_le_one.mpr
  intro x hx y hy
  apply Subtype.ext
  apply card_le_one.mp hcard
  · have hh := mem_filter.mp hx
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a x.val).mpr ((Mole.mem_dartsAt _ a x).mp hh.1),hh.2⟩
  · have hh := mem_filter.mp hy
    exact mem_filter.mpr ⟨(Mole.mem_dartsAt M a y.val).mpr ((Mole.mem_dartsAt _ a y).mp hh.1),hh.2⟩

/-- A connected induced group containing an actual unsaturated vertex is
itself a molecule. All oriented caps are inherited from the old graph. -/
theorem induced_isMolecule_of_connected_degree_ne_four (M : Molecule V D) (hM : M.IsMolecule)
    (U : Finset V) (hU : U ⊆ M.atoms)
    (hconn : ∀ a ∈ U, ∀ b ∈ U, (Mole.induced M U).SameComponent a b)
    {p : V} (hp : p ∈ U) (hp4 : (Mole.induced M U).deg p ≠ 4) :
    (Mole.induced M U).IsMolecule := by
  constructor
  · intro z hz
    exact ⟨(card_filtered_dartsAt_induced_le M U z (fun x => M.out x = true)).trans (hM.1 z (hU hz)).1,
      (card_filtered_dartsAt_induced_le M U z (fun x => M.out x = false)).trans (hM.1 z (hU hz)).2⟩
  · intro z hz
    exact ⟨p,hp,hconn z hz p hp,hp4⟩

end WaveTurbulence.MoleProp
