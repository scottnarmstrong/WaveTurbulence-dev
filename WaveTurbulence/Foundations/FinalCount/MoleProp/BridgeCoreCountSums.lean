/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeCore
import Mathlib.Tactic

/-! # Exact local source sums before and after deleting a bond -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

noncomputable def bridgeRemovedDartsAt (M : Molecule V D) (v : V) : Finset D :=
  by classical exact (M.dartsAt v).filter (fun x => Degen.IsBridge M x)

theorem sum_dartsAt_bridgeCore_add_removed (M : Molecule V D) (v : V)
    {A : Type*} [AddCommMonoid A] (g : D → A) :
    (∑ x ∈ (bridgeCore M).dartsAt v, g x.val) +
      (∑ x ∈ bridgeRemovedDartsAt M v, g x) = ∑ x ∈ M.dartsAt v, g x := by
  classical
  have hs : (∑ x ∈ (bridgeCore M).dartsAt v, g x.val) =
      ∑ x ∈ (M.dartsAt v).filter (fun x => ¬ Degen.IsBridge M x), g x := by
    apply sum_bij (fun x _ => x.val)
    · intro x hx
      exact mem_filter.mpr ⟨(Mole.mem_dartsAt M v x.val).mpr
        ((Mole.mem_dartsAt _ v x).mp hx),x.property⟩
    · intro x _ y _ h
      exact Subtype.ext h
    · intro y hy
      obtain ⟨hya,hyp⟩ := mem_filter.mp hy
      exact ⟨⟨y,hyp⟩,(Mole.mem_dartsAt _ v _).mpr ((Mole.mem_dartsAt M v y).mp hya),rfl⟩
    · intro x _; rfl
  rw [hs]
  simpa only [bridgeRemovedDartsAt,not_not] using sum_filter_add_sum_filter_not (M.dartsAt v) (fun x => ¬ Degen.IsBridge M x) g

end WaveTurbulence.MoleProp
