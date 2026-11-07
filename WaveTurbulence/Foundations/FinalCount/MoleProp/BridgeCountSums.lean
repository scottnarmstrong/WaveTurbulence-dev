/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.Prop103BridgeDeletion
import Mathlib.Tactic

/-! # Exact local source sums before and after deleting a bond -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def bondRemovedDartsAt (M : Molecule V D) (e : D) (v : V) : Finset D :=
  (M.dartsAt v).filter (fun x => ¬ (x ≠ e ∧ x ≠ M.mate e))

theorem sum_dartsAt_eraseBond_add_removed (M : Molecule V D) (e : D) (v : V)
    {A : Type*} [AddCommMonoid A] (g : D → A) :
    (∑ x ∈ (eraseBond M e).dartsAt v, g x.val) +
      (∑ x ∈ bondRemovedDartsAt M e v, g x) = ∑ x ∈ M.dartsAt v, g x := by
  classical
  have hs : (∑ x ∈ (eraseBond M e).dartsAt v, g x.val) =
      ∑ x ∈ (M.dartsAt v).filter (fun x => x ≠ e ∧ x ≠ M.mate e), g x := by
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
  exact sum_filter_add_sum_filter_not _ _ _

theorem bond_removed_labels_eq (M : Molecule V D) (e : D) {K : Type*}
    {κ κ0 : D → K} (hb : ∀ x, κ (M.mate x) = κ x)
    (hb0 : ∀ x, κ0 (M.mate x) = κ0 x) (he : κ e = κ0 e)
    {v : V} {x : D} (hx : x ∈ bondRemovedDartsAt M e v) : κ x = κ0 x := by
  have hx' := (mem_filter.mp hx).2
  push Not at hx'
  by_cases hxe : x = e
  · exact hxe ▸ he
  · have hxm : x = M.mate e := hx' hxe
    simpa only [hxm,hb,hb0] using he

end WaveTurbulence.MoleProp
