/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Ports
public import Mathlib.Logic.Equiv.Set

/-! # Extending an exact port matching by inactive labels

Conjugate the matching onto the image of an embedding; every label outside
that image is an inactive identity. The inverse on the image is Mathlib's
unique inverse of an injective function, not a choice of a matching.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

open Classical in
/-- Exact matching extension: conjugation on the image and inactive identities outside it. -/
noncomputable def extendMate {α β : Type*} (f : α ↪ β) (m : α → α) (x : β) : β :=
  if h : x ∈ Set.range f then f (m ((Equiv.ofInjective f f.injective).symm ⟨x,h⟩)) else x

/-- Every original matching edge is retained exactly on the embedded ports. -/
theorem extendMate_apply {α β : Type*} (f : α ↪ β) (m : α → α) (a : α) :
    extendMate f m (f a) = f (m a) := by
  classical
  rw [extendMate,dite_eq_left (show f a ∈ Set.range f from ⟨a,rfl⟩)]
  rw [Equiv.ofInjective_symm_apply]

/-- Unused labels have their literal inactive meaning. -/
theorem extendMate_outside {α β : Type*} (f : α ↪ β) (m : α → α) (x : β)
    (hx : x ∉ Set.range f) : extendMate f m x = x := by
  classical
  rw [extendMate,dite_eq_right hx]

/-- Adding inactive labels preserves the original matching involution. -/
theorem extendMate_involutive {α β : Type*} (f : α ↪ β) (m : α → α)
    (hm : Function.Involutive m) : Function.Involutive (extendMate f m) := by
  intro x
  by_cases hx : x ∈ Set.range f
  · obtain ⟨a,rfl⟩ := hx
    rw [extendMate_apply,extendMate_apply,hm a]
  · rw [extendMate_outside f m x hx,extendMate_outside f m x hx]

/-- Embedded ports keep exactly their original active/inactive status. -/
theorem extendMate_fixed_iff {α β : Type*} (f : α ↪ β) (m : α → α) (a : α) :
    extendMate f m (f a) = f a ↔ m a = a := by
  rw [extendMate_apply]
  exact f.injective.eq_iff

/-- If all original ports are active, the active-label set is exactly the embedding's range. -/
theorem extendMate_active_iff {α β : Type*} (f : α ↪ β) (m : α → α)
    (ha : ∀ a, m a ≠ a) (x : β) : extendMate f m x ≠ x ↔ x ∈ Set.range f := by
  constructor
  · intro hx
    by_contra hn
    exact hx (extendMate_outside f m x hn)
  · rintro ⟨a,rfl⟩ he
    exact ha a ((extendMate_fixed_iff f m a).mp he)

end WaveTurbulence.Reg.Skeleton
