/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBReinsertion
import Mathlib.Tactic

/-! # Exact local sums after adding a directed bond -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reindex all old and new incidences. Loops correctly contribute twice. -/
theorem appb_sum_dartsAt_addBond (M : Molecule V D) (a b v : V)
    {A : Type*} [AddCommMonoid A] (g : D ⊕ Bool → A) :
    (∑ x ∈ (addBond M a b).dartsAt v, g x) =
      (∑ x ∈ M.dartsAt v, g (.inl x)) +
      (if a = v then g (.inr true) else 0) + (if b = v then g (.inr false) else 0) := by
  let p : D ⊕ Bool → Prop := fun x => (addBond M a b).atom x = v
  have he : univ.filter p = (univ.filter (fun x : D => p (.inl x))).disjSum
      (univ.filter (fun x : Bool => p (.inr x))) := by
    ext x
    cases x <;> simp
  change (∑ x ∈ univ.filter p, g x) = _
  rw [he,sum_disjSum]
  change (∑ x ∈ M.dartsAt v, g (.inl x)) +
    (∑ x ∈ (univ : Finset Bool).filter (fun t => (if t then a else b) = v), g (.inr x)) = _
  rw [show (univ : Finset Bool) = {true,false} by decide, sum_filter]
  by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha,hb,add_assoc]

end WaveTurbulence.Mole
