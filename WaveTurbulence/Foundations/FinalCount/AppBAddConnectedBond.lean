/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBAddEraseIso
import Mathlib.Tactic

/-! # Reinsertion inside an existing component does not change F -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The actual component-quotient equivalence for a bond added between
already connected surviving vertices. -/
@[expose] noncomputable def appbAddConnectedBondEquiv (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : M.SameComponent a b) :
    AppbComponents M ≃ AppbComponents (addBond M a b) := by
  let N := addBond M a b
  let f : M.atoms ≃ N.atoms := (appbEraseAddedBondIso M a b ha hb).atoms
  have hf (v : M.atoms) : (f v).val = v.val := rfl
  have hg (v : N.atoms) : (f.symm v).val = v.val := rfl
  have hforward : ∀ u v : M.atoms, M.Adj u.val v.val → N.Adj (f u).val (f v).val := by
    intro u v h
    obtain ⟨x,hx,hy⟩ := h
    exact ⟨.inl x,hx,hy⟩
  have hback : ∀ u v : N.atoms, N.Adj u.val v.val → M.SameComponent (f.symm u).val (f.symm v).val := by
    intro u v h
    obtain ⟨x,hx,hy⟩ := h
    rw [hg,hg]
    cases x with
    | inl x => exact Relation.EqvGen.rel _ _ ⟨x,hx,hy⟩
    | inr t =>
      cases t
      · change b = u.val at hx
        change a = v.val at hy
        rw [← hx,← hy]
        exact hab.symm
      · change a = u.val at hx
        change b = v.val at hy
        rw [← hx,← hy]
        exact hab
  let forward : AppbComponents M → AppbComponents N := Quot.map f hforward
  let backward : AppbComponents N → AppbComponents M := Quot.lift
    (fun v => appbComponent M (f.symm v)) (by
      intro u v h
      exact quotient_eq_of_sameComponent M (hback u v h) (f.symm u).property (f.symm v).property)
  exact {
    toFun := forward
    invFun := backward
    left_inv := by
      intro q
      induction q using Quot.inductionOn with | h v =>
        change appbComponent M (f.symm (f v)) = appbComponent M v
        rw [f.symm_apply_apply]
    right_inv := by
      intro q
      induction q using Quot.inductionOn with | h v =>
        change appbComponent N (f (f.symm v)) = appbComponent N v
        rw [f.apply_symm_apply] }

/-- Exact component invariance in the two reinsertion operations. -/
theorem appb_addBond_components_of_connected (M : Molecule V D) (a b : V)
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) (hab : M.SameComponent a b) :
    (addBond M a b).numComponents = M.numComponents :=
  (Nat.card_congr (appbAddConnectedBondEquiv M a b ha hb hab)).symm

end WaveTurbulence.Mole
