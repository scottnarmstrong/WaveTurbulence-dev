/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineRemovalExternalEdges
public import WaveTurbulence.Foundations.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic

/-! # Removing a hyper-block's adjoint preserves connectivity -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [DecidableEq D] [Fintype D]

/-- TARGET subsetvc, single adjoint-removal connectivity: every path can
be retracted across the removed interior using the retained added bond.
This applies to any connected ambient atomic group containing the hyper-block. -/
theorem adjoint_removal_connected (M : Molecule V D) (hM : M.IsMolecule)
    {S A : Finset V} (hS : GroupConnected M S) (hAS : A ⊆ S)
    {a b : V} (e : D) (he : M.ends e=s(a,b))
    (hB : (Mole.eraseBond M e).IsBlock A a b) :
    ∀ u ∈ remainingAtoms S [adjointRemoval M A a b e],
      ∀ v ∈ remainingAtoms S [adjointRemoval M A a b e],
        (removeBlocks M S [adjointRemoval M A a b e]).SameComponent u v := by
  let P := adjointRemoval M A a b e
  let N := removeBlocks M S [P]
  let r : V → V := fun v => if v ∈ P.interior then a else v
  have haS : a ∈ S := hAS hB.2.1
  have hbS : b ∈ S := hAS hB.2.2.1
  have hH : Mole.IsHyperBlock M A a b := ⟨e,he,hB⟩
  have hint := (Mole.hyperBlock_degrees M hH).2.2
  have hpath : N.SameComponent a b := Relation.EqvGen.rel _ _
    (adjointRemoval_added_adj M S A a b e haS hbS he)
  have hjpath : ∀ x ∈ ({a,b} : Finset V),∀ y ∈ ({a,b} : Finset V),N.SameComponent x y := by
    intro x hx y hy
    simp only [mem_insert,mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact hpath
    · exact Relation.EqvGen.symm _ _ hpath
    · exact Relation.EqvGen.refl _
  have hrjoint : ∀ v ∈ A,r v ∈ ({a,b} : Finset V) := by
    intro v hv
    by_cases hi : v ∈ P.interior
    · simp only [r,hi,ite_true,mem_insert,mem_singleton,true_or]
    · have hj : v ∈ ({a,b} : Finset V) := by
        by_contra hh
        exact hi (mem_sdiff.mpr ⟨hv,hh⟩)
      simpa only [r,hi,ite_false] using hj
  have hclosed : ∀ u ∈ P.interior,∀ v,M.Adj u v → v ∈ A := by
    intro u hu v huv
    have huint := mem_sdiff.mp hu
    change u ∈ A ∧ u ∉ ({a,b} : Finset V) at huint
    have hne : u ≠ a ∧ u ≠ b := by
      simpa only [mem_insert,mem_singleton,not_or] using huint.2
    obtain ⟨d,hdu,hdv⟩ := huv
    have hh := Mole.full_degree_no_exit M hM (hB.1 huint.1)
      (hint u huint.1 hne.1 hne.2) hdu
    exact hdv ▸ hh
  have hedge : ∀ u v,(Mole.induced M S).Adj u v → N.SameComponent (r u) (r v) := by
    intro u v huv
    obtain ⟨hadj,huS,hvS⟩ := (Mole.induced_adj_iff M S u v).mp huv
    by_cases hboth : u ∈ A ∧ v ∈ A
    · exact hjpath _ (hrjoint u hboth.1) _ (hrjoint v hboth.2)
    · have hui : u ∉ P.interior := by
        intro hi
        exact hboth ⟨(mem_sdiff.mp hi).1,hclosed u hi v hadj⟩
      have hvi : v ∉ P.interior := by
        intro hi
        exact hboth ⟨hclosed v hi u (Mole.adj_symmetric M hadj),(mem_sdiff.mp hi).1⟩
      simp only [r,hui,hvi,ite_false]
      exact Relation.EqvGen.rel _ _ (adjointRemoval_external_adj M S A a b e huS hvS hui hvi hboth hadj)
  have lift : ∀ u v,(Mole.induced M S).SameComponent u v → N.SameComponent (r u) (r v) := by
    intro u v hp
    induction hp with
    | rel u v huv => exact hedge u v huv
    | refl u => exact Relation.EqvGen.refl _
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  intro u hu v hv
  have huS := (mem_filter.mp hu).1
  have hvS := (mem_filter.mp hv).1
  have hui : u ∉ P.interior := (mem_filter.mp hu).2 P List.mem_cons_self
  have hvi : v ∉ P.interior := (mem_filter.mp hv).2 P List.mem_cons_self
  have hp := lift u v (hS u huS v hvS)
  simpa only [r,hui,hvi,ite_false] using hp

end WaveTurbulence.Vine
