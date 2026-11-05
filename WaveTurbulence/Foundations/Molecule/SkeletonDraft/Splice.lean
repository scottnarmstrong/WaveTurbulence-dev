/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PortOverlap

/-! # Exact half-edge splicing for matching contractions

Delete two halfedges and connect their previous partners. Deleted halfedges
become inactive fixed points. If the deleted halfedges were already matched,
this just deletes that edge. These are auxiliary literal matching operations;
the source mini-piece correspondence is proved separately.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Remove two ports, joining their surviving partners and retaining every other edge. -/
def splice {α : Type*} [DecidableEq α] (mate : α → α) (a b x : α) : α :=
  if x = a ∨ x = b then x
  else if mate x = a then mate b
  else if mate x = b then mate a
  else mate x

@[simp] theorem splice_left {α : Type*} [DecidableEq α] (mate : α → α) (a b : α) :
    splice mate a b a = a := by simp [splice]

@[simp] theorem splice_right {α : Type*} [DecidableEq α] (mate : α → α) (a b : α) :
    splice mate a b b = b := by simp [splice]

/-- An already inactive port remains inactive. -/
theorem splice_fixed {α : Type*} [DecidableEq α] (mate : α → α) (a b x : α)
    (hx : mate x = x) : splice mate a b x = x := by
  by_cases ha : x = a
  · subst x; exact splice_left mate a b
  by_cases hb : x = b
  · subst x; exact splice_right mate a b
  simp [splice,ha,hb,hx]

/-- Splicing forgets the order of the two ports being removed. -/
theorem splice_symm {α : Type*} [DecidableEq α] (mate : α → α) (a b : α) :
    splice mate a b = splice mate b a := by
  funext x
  by_cases hab : a = b
  · subst b; rfl
  by_cases ha : x = a
  · subst x; simp
  by_cases hb : x = b
  · subst x; simp
  by_cases hma : mate x = a
  · simp [splice,ha,hb,hma,hab]
  by_cases hmb : mate x = b
  · simp [splice,ha,hb,hmb,Ne.symm hab]
  simp [splice,ha,hb,hma,hmb]

/-- Two active distinct ports can be removed without breaking matching involutivity. -/
theorem splice_involutive {α : Type*} [DecidableEq α] (mate : α → α)
    (hm : Function.Involutive mate) (a b : α) (hab : a ≠ b)
    (ha : mate a ≠ a) (hb : mate b ≠ b) : Function.Involutive (splice mate a b) := by
  intro x
  by_cases hxa : x = a
  · subst x; simp
  by_cases hxb : x = b
  · subst x; simp
  by_cases hma : mate x = a
  · have hax : mate a = x := by have h := hm x; rw [hma] at h; exact h
    have hba : mate b ≠ a := by
      intro h
      exact hxb (hm.injective (h.trans hma.symm)).symm
    simp [splice,hxa,hxb,hma,hba,hb,hm b,hax,Ne.symm hab]
  by_cases hmb : mate x = b
  · have hbx : mate b = x := by have h := hm x; rw [hmb] at h; exact h
    have hab' : mate a ≠ b := by
      intro h
      exact hxa (hm.injective (h.trans hmb.symm)).symm
    simp [splice,hxa,hxb,hmb,hab',ha,hm a,hbx,Ne.symm hab]
  · simp [splice,hxa,hxb,hma,hmb,hm x]

end WaveTurbulence.Reg.Skeleton
