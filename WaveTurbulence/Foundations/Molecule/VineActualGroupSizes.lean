/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineActualPartition
import Mathlib.Tactic

/-! # Actual coherence groups have the prescribed sizes (TARGET cohmol) -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Pullback along the exact realization preserves each group's size. -/
theorem realized_group_length {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) {g : List ℕ} (hg : g ∈ (X.expand R.k).groups) :
    (S.toList.filter fun v => R.f v ∈ g).length=g.length := by
  let G := S.filter fun v => R.f v ∈ g
  have hi : G.image R.f=g.toFinset := by
    ext i
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := mem_image.mp h
      exact List.mem_toFinset.mpr (mem_filter.mp hv).2
    · intro h
      have hig : i ∈ g := List.mem_toFinset.mp h
      have hflat := List.mem_flatten.mpr ⟨g,hg,hig⟩
      have hrange := (mem_expand_groups_iff X R.k i).mp hflat
      have himage : i ∈ S.image R.f := R.image_eq.symm ▸ mem_range.mpr hrange.2
      obtain ⟨v,hv,hvi⟩ := mem_image.mp himage
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hvi.symm ▸ hig⟩,hvi⟩
  have hcount := congrArg Finset.card hi
  have hinj : Set.InjOn R.f G := R.injOn.mono (filter_subset _ _)
  rw [card_image_of_injOn hinj] at hcount
  have hgn := (List.nodup_flatten.mp (expand_groups_nodup X R.k)).1 g hg
  rw [List.toFinset_card_of_nodup hgn] at hcount
  have hf : (S.toList.filter fun v => R.f v ∈ g).toFinset=G := by
    ext v
    simp only [List.mem_toFinset,List.mem_filter,Finset.mem_toList,decide_eq_true_eq,G,mem_filter]
  have hl := List.toFinset_card_of_nodup (S.nodup_toList.filter (fun v => decide (R.f v ∈ g)))
  rw [hf] at hl
  exact hl.symm.trans hcount

/-- TARGET cohmol: every actual group has two or three atoms. -/
theorem realized_group_sizes {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) :
    ∀ g ∈ realizedGroups R, g.length=2 ∨ g.length=3 := by
  intro g hg
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  rw [realized_group_length R hg0]
  exact expand_group_sizes X R.k g0 hg0

/-- The actual incoherency index obeys the same exact group-count bound. -/
theorem realized_index_le {L : Type*} [DecidableEq L]
    {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V}
    (R : VineRealization M X S a b) (layer : V → L) :
    realizedIncoherencyIndex R layer ≤ X.template.groups.length+R.k.sum := by
  have hh := incoherencyIndex_le layer (realizedGroups R)
  simpa only [realizedIncoherencyIndex,realizedGroups,List.length_map,expand_groups_exact X R.k R.length_eq] using hh

end WaveTurbulence.Vine
