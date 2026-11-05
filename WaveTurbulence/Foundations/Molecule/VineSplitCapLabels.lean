/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineCapBijection
import Mathlib.Tactic

/-! # Packing two separated triangle-cap rail allocations into consecutive labels -/

public section
namespace WaveTurbulence.Vine
open Finset

/-- A triangle cap whose two r-rung allocations may have unused labels
between them, as happens when only a prefix of a longer ladder is selected. -/
@[expose] def splitCapLabels (N P r : ℕ) : Finset ℕ :=
  {4,5,6} ∪ (range r).image (N+·) ∪ (range r).image (P+·)

/-- Membership keeps the triangle and both precise allocation intervals. -/
theorem mem_splitCapLabels_iff (N P r a : ℕ) : a ∈ splitCapLabels N P r ↔
    a=4 ∨ a=5 ∨ a=6 ∨ (N ≤ a ∧ a<N+r) ∨ (P ≤ a ∧ a<P+r) := by
  have himage (Q : ℕ) : a ∈ (range r).image (Q+·) ↔ Q ≤ a ∧ a<Q+r := by
    constructor
    · intro ha
      obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
      have := mem_range.mp hi
      constructor <;> omega
    · rintro ⟨hlo,hhi⟩
      exact mem_image.mpr ⟨a-Q,mem_range.mpr (by omega),by omega⟩
  simp only [splitCapLabels,mem_union,mem_insert,mem_singleton,himage,or_assoc]

/-- Shift only the lower selected rail into the packed lower allocation.
Outside that selected interval this is the identity. -/
@[expose] def packCapLabel (N P r a : ℕ) : ℕ :=
  if P ≤ a ∧ a<P+r then N+r+(a-P) else a

/-- The inverse restores the original lower allocation; outside the packed
lower interval this is the identity. -/
@[expose] def unpackCapLabel (N P r a : ℕ) : ℕ :=
  if N+r ≤ a ∧ a<N+2*r then P+(a-(N+r)) else a

/-- Packing maps selected source labels into the exact contiguous cap set. -/
theorem packCapLabel_mem (N P r a : ℕ) (hN : 9 ≤ N) (hsep : N+r ≤ P)
    (ha : a ∈ splitCapLabels N P r) : packCapLabel N P r a ∈ capLabels N r := by
  rw [mem_splitCapLabels_iff] at ha
  rw [mem_capLabels_iff]
  unfold packCapLabel
  split_ifs <;> omega

/-- Packing followed by unpacking recovers every selected source label. -/
theorem unpack_packCapLabel (N P r a : ℕ) (hN : 9 ≤ N) (hsep : N+r ≤ P)
    (ha : a ∈ splitCapLabels N P r) : unpackCapLabel N P r (packCapLabel N P r a)=a := by
  rw [mem_splitCapLabels_iff] at ha
  unfold packCapLabel unpackCapLabel
  split_ifs <;> omega

/-- Unpacking lands in the selected source label set. -/
theorem unpackCapLabel_mem (N P r a : ℕ) (hN : 9 ≤ N) (hsep : N+r ≤ P)
    (ha : a ∈ capLabels N r) : unpackCapLabel N P r a ∈ splitCapLabels N P r := by
  rw [mem_capLabels_iff] at ha
  rw [mem_splitCapLabels_iff]
  unfold unpackCapLabel
  split_ifs <;> omega

/-- Unpacking followed by packing recovers every contiguous cap label. -/
theorem pack_unpackCapLabel (N P r a : ℕ) (hN : 9 ≤ N) (hsep : N+r ≤ P)
    (ha : a ∈ capLabels N r) : packCapLabel N P r (unpackCapLabel N P r a)=a := by
  rw [mem_capLabels_iff] at ha
  unfold packCapLabel unpackCapLabel
  split_ifs <;> omega

/-- The explicit packing exhausts precisely the contiguous cap labels. -/
theorem packCapLabel_image (N P r : ℕ) (hN : 9 ≤ N) (hsep : N+r ≤ P) :
    (splitCapLabels N P r).image (packCapLabel N P r)=capLabels N r := by
  ext a
  constructor
  · intro ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    exact packCapLabel_mem N P r b hN hsep hb
  · intro ha
    exact mem_image.mpr ⟨unpackCapLabel N P r a,unpackCapLabel_mem N P r a hN hsep ha,
      pack_unpackCapLabel N P r a hN hsep ha⟩

end WaveTurbulence.Vine
