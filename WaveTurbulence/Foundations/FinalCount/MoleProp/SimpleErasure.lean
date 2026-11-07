/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SimpleNormalization
public import WaveTurbulence.Foundations.FinalCount.Degen.LadderDeletionGeometry
import Mathlib.Tactic

/-! # Source simplicity and component closure under literal atom erasure -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem bondsBetween_eraseAtoms_le (M : Molecule V D) (Y : Finset V)
    {a b : V} (hab : a ≠ b) :
    (Degen.eraseAtoms M Y).bondsBetween a b ≤ M.bondsBetween a b := by
  classical
  have hsub : ((Degen.neighborDarts (Degen.eraseAtoms M Y) a b).image
      (fun x => x.val)) ⊆ Degen.neighborDarts M a b := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
    obtain ⟨hya,hyb⟩ := mem_filter.mp hy
    apply mem_filter.mpr
    exact ⟨(Mole.mem_dartsAt M a y.val).mpr ((Mole.mem_dartsAt _ a y).mp hya),hyb⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ Subtype.val_injective,
    Degen.card_neighborDarts _ hab,Degen.card_neighborDarts _ hab] at hh
  exact hh

theorem simple_eraseAtoms (M : Molecule V D) (Y : Finset V)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ∀ a b, a ≠ b → (Degen.eraseAtoms M Y).bondsBetween a b ≤ 1 := by
  intro a b hab
  exact (bondsBetween_eraseAtoms_le M Y hab).trans (hsimple a b hab)

theorem sameComponent_eraseAtoms_imp (M : Molecule V D) (Y : Finset V)
    {a b : V} (h : (Degen.eraseAtoms M Y).SameComponent a b) : M.SameComponent a b := by
  induction h with
  | rel a b hab =>
    obtain ⟨x,hxa,hxb⟩ := hab
    exact Relation.EqvGen.rel _ _ ⟨x.val,hxa,hxb⟩
  | refl a => exact Relation.EqvGen.refl a
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- A simple source graph never enables operation(b). -/
theorem no_operation_b_of_simple (M : Molecule V D)
    (hsimple : ∀ a b, a ≠ b → M.bondsBetween a b ≤ 1) :
    ¬ ∃ a ∈ M.atoms, ∃ b ∈ M.atoms, a ≠ b ∧ M.deg a = 3 ∧
      (M.deg b = 3 ∨ M.deg b = 4) ∧ M.bondsBetween a b = 2 := by
  rintro ⟨a,_ha,b,_hb,hab,_ha3,_hb34,hd⟩
  have hh := hsimple a b hab
  omega

end WaveTurbulence.MoleProp
