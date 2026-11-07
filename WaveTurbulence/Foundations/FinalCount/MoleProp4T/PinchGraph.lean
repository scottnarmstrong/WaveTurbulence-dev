/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Pinch
import Mathlib.Tactic

/-! # The contracted molecule of a pinch: stars, caps, connectivity, circuit rank -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

/-- A dart at an atom of `Y` touches `Y`. -/
def dartOf (z : D) (hz : N.atom z ∈ T.Y) : MoleProp.DeletedDart N T.Y := ⟨z, fun h => h.1 hz⟩

theorem aux_atom_some {z : MoleProp.DeletedDart N T.Y} {v : V} :
    T.aux.atom z = some v ↔ N.atom z.val = v ∧ v ∈ T.Y := by
  change (if N.atom z.val ∈ T.Y then some (N.atom z.val) else none) = some v ↔ _
  split_ifs with h
  · simp only [Option.some.injEq]; constructor
    · rintro rfl; exact ⟨rfl, h⟩
    · rintro ⟨rfl, _⟩; rfl
  · simp only [false_iff, not_and]; rintro rfl; exact h

theorem aux_atom_none {z : MoleProp.DeletedDart N T.Y} : T.aux.atom z = none ↔ N.atom z.val ∉ T.Y := by
  change (if N.atom z.val ∈ T.Y then some (N.atom z.val) else none) = none ↔ _
  split_ifs with h <;> simp [h]

/-- The darts at `none` are the mates of the exits. -/
theorem aux_dartsAt_none :
    T.aux.dartsAt none = {⟨N.mate T.x, fun h => h.2 (by rw [N.mate_mate]; exact T.atom_x)⟩,
      ⟨N.mate T.y, fun h => h.2 (by rw [N.mate_mate]; exact T.atom_y)⟩} := by
  ext z
  simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_insert, mem_singleton, T.aux_atom_none]
  constructor
  · intro hz
    have hz' := z.property
    have hmY : N.atom (N.mate z.val) ∈ T.Y := by by_contra h; exact hz' ⟨hz, h⟩
    have h := (show N.mate z.val ∈ crossDarts N T.Y from mem_crossDarts.mpr ⟨hmY, by rw [N.mate_mate]; exact hz⟩)
    rw [T.cross] at h
    simp only [mem_insert, mem_singleton] at h
    rcases h with h | h
    · left; apply Subtype.ext; change z.val = N.mate T.x; rw [← h, N.mate_mate]
    · right; apply Subtype.ext; change z.val = N.mate T.y; rw [← h, N.mate_mate]
  · rintro (rfl | rfl)
    · change N.atom (N.mate T.x) ∉ T.Y; exact T.w_notMem
    · change N.atom (N.mate T.y) ∉ T.Y; rw [← T.same]; exact T.w_notMem

/-- Star sums at an atom of `Y` are those of `N`. -/
theorem aux_sum_some {v : V} (hv : v ∈ T.Y) {E : Type*} [AddCommMonoid E] (f : D → E) :
    ∑ z ∈ T.aux.dartsAt (some v), f z.val = ∑ z ∈ N.dartsAt v, f z := by
  refine sum_bij (fun z _ => z.val) ?_ ?_ ?_ ?_
  · intro z hz
    have := (T.aux_atom_some.mp (mem_filter.mp hz).2).1
    exact mem_filter.mpr ⟨mem_univ _, this⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro z hz
    have hzv : N.atom z = v := (mem_filter.mp hz).2
    refine ⟨T.dartOf z (hzv ▸ hv), mem_filter.mpr ⟨mem_univ _, T.aux_atom_some.mpr ⟨hzv, hv⟩⟩, rfl⟩
  · intro _ _; rfl

theorem mate_x_ne_mate_y : N.mate T.x ≠ N.mate T.y := fun h => T.ne (by
  have := congrArg N.mate h; rwa [N.mate_mate, N.mate_mate] at this)

/-- Star sums at `none`. -/
theorem aux_sum_none {E : Type*} [AddCommMonoid E] (f : D → E) :
    ∑ z ∈ T.aux.dartsAt none, f z.val = f (N.mate T.x) + f (N.mate T.y) := by
  rw [T.aux_dartsAt_none, sum_pair]
  intro h; exact T.mate_x_ne_mate_y (congrArg Subtype.val h)

/-- `aux` satisfies the in/out caps. -/
theorem aux_caps (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) :
    ∀ o ∈ T.aux.atoms, T.aux.outdeg o ≤ 2 ∧ T.aux.indeg o ≤ 2 := by
  classical
  intro o ho
  have hcard : ∀ (o : Option V) (b : Bool), ((T.aux.dartsAt o).filter fun z => T.aux.out z = b).card =
      ∑ z ∈ T.aux.dartsAt o, (if N.out z.val = b then 1 else 0) := by
    intro o b; rw [card_filter]; rfl
  rcases o with _ | v
  · have h1 := (hcard none true).trans (T.aux_sum_none (fun z => if N.out z = true then 1 else 0))
    have h2 := (hcard none false).trans (T.aux_sum_none (fun z => if N.out z = false then 1 else 0))
    simp [N.out_mate, T.out_x, T.out_y] at h1 h2
    unfold Molecule.outdeg Molecule.indeg
    rw [h1, h2]; norm_num
  · have hv : v ∈ T.Y := by
      simp only [aux, mem_insert, reduceCtorEq, mem_image, Option.some.injEq, exists_eq_right, false_or] at ho
      exact ho
    have hc := fun b => hcard (some v) b
    have hN := hcap v (T.sub hv)
    unfold Molecule.outdeg Molecule.indeg at hN ⊢
    rw [hc true, hc false, T.aux_sum_some hv (fun z => if N.out z = true then 1 else 0),
      T.aux_sum_some hv (fun z => if N.out z = false then 1 else 0), ← card_filter, ← card_filter]
    exact hN

end Pinch
end WaveTurbulence.MoleProp4
