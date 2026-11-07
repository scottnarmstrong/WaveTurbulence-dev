/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBondErasure
import Mathlib.Tactic

/-! # Exact retained and deleted incidence sums for bridge removal -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Reindex the retained incidences by their old darts. -/
theorem appb_sum_dartsAt_eraseBond (M : Molecule V D) (e : D) (v : V)
    {A : Type*} [AddCommMonoid A] (g : D → A) :
    (∑ x ∈ (eraseBond M e).dartsAt v, g x.val) =
      ∑ x ∈ (M.dartsAt v).filter (fun x => x ≠ e ∧ x ≠ M.mate e), g x := by
  apply sum_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,x.property⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro x hx
    obtain ⟨hx,hp⟩ := mem_filter.mp hx
    exact ⟨⟨x,hp⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hx).2⟩,rfl⟩
  · intro x _; rfl

/-- Deleting one bond subtracts exactly its two signed incidences, even
when both incidences belong to the same atom. -/
theorem appb_sum_dartsAt_bond_split (M : Molecule V D) (e : D) (v : V)
    {A : Type*} [AddCommMonoid A] (g : D → A) :
    (∑ x ∈ (eraseBond M e).dartsAt v, g x.val) +
      (if M.atom e = v then g e else 0) + (if M.atom (M.mate e) = v then g (M.mate e) else 0) =
      ∑ x ∈ M.dartsAt v, g x := by
  rw [appb_sum_dartsAt_eraseBond]
  have hh := sum_filter_add_sum_filter_not (M.dartsAt v) (fun x => x ≠ e ∧ x ≠ M.mate e) g
  have he : (M.dartsAt v).filter (fun x => ¬(x ≠ e ∧ x ≠ M.mate e)) =
      ({e,M.mate e} : Finset D).filter (fun x => M.atom x = v) := by
    ext x
    simp only [Molecule.dartsAt,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    tauto
  have hd : (∑ x ∈ ({e,M.mate e} : Finset D).filter (fun x => M.atom x = v), g x) =
      (if M.atom e = v then g e else 0) + (if M.atom (M.mate e) = v then g (M.mate e) else 0) := by
    rw [sum_filter,sum_pair (M.mate_ne e).symm]
  rw [he,hd] at hh
  simpa only [add_assoc] using hh

end WaveTurbulence.Mole
