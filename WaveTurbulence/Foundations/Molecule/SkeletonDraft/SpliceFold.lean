/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceActivity
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceCommutation

/-! # Finite port deletion: matching and activity invariants -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- The literal ports deleted by a list of splices. -/
def pairPorts {α : Type*} (P : List (α × α)) : List α := P.flatMap fun p => [p.1,p.2]

theorem pairPorts_cons {α : Type*} (p : α × α) (P : List (α × α)) :
    pairPorts (p::P) = p.1 :: p.2 :: pairPorts P := rfl

/-- Apply the indicated halfedge splices in the given order. -/
def foldSplice {α : Type*} [DecidableEq α] (m : α → α) : List (α × α) → α → α
  | [] => m
  | p::P => foldSplice (splice m p.1 p.2) P

/-- Previously inactive halfedges remain inactive throughout any finite splice list. -/
theorem foldSplice_fixed {α : Type*} [DecidableEq α] (P : List (α × α)) (m : α → α)
    (x : α) (hx : m x = x) : foldSplice m P x = x := by
  induction P generalizing m with
  | nil => exact hx
  | cons p P ih => exact ih _ (splice_fixed m p.1 p.2 x hx)

/-- Every deleted halfedge is inactive after the complete list, even if listed more than once. -/
theorem foldSplice_target_fixed {α : Type*} [DecidableEq α] (P : List (α × α)) (m : α → α)
    (x : α) (hx : x ∈ pairPorts P) : foldSplice m P x = x := by
  induction P generalizing m with
  | nil => simp [pairPorts] at hx
  | cons p P ih =>
    rw [pairPorts_cons] at hx
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact foldSplice_fixed P _ _ (splice_left m p.1 p.2)
    · rcases List.mem_cons.mp h with h | h
      · subst x
        exact foldSplice_fixed P _ _ (splice_right m p.1 p.2)
      · exact ih _ h

/-- A surviving edge whose two endpoints avoid the deleted ports is unchanged. -/
theorem foldSplice_unaffected {α : Type*} [DecidableEq α] (P : List (α × α)) (m : α → α)
    (x : α) (hx : x ∉ pairPorts P) (hmx : m x ∉ pairPorts P) : foldSplice m P x = m x := by
  induction P generalizing m with
  | nil => rfl
  | cons p P ih =>
    have h1 : x ≠ p.1 ∧ x ≠ p.2 ∧ x ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hx
    have h2 : m x ≠ p.1 ∧ m x ≠ p.2 ∧ m x ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hmx
    have he := splice_unaffected m p.1 p.2 x h1.1 h1.2.1 h2.1 h2.2.1
    have hi := ih (splice m p.1 p.2) h1.2.2 (by rw [he]; exact h2.2.2)
    exact hi.trans he

/-- A disjoint list of active-port splices preserves matching involutivity and
creates no inactive ports outside the listed targets. -/
theorem foldSplice_properties {α : Type*} [DecidableEq α] (P : List (α × α)) (m : α → α)
    (hm : Function.Involutive m) (hP : (pairPorts P).Nodup)
    (ha : ∀ x ∈ pairPorts P, m x ≠ x) :
    Function.Involutive (foldSplice m P) ∧
      ∀ x, x ∉ pairPorts P → (foldSplice m P x = x ↔ m x = x) := by
  induction P generalizing m with
  | nil => exact ⟨hm,fun _ _ => Iff.rfl⟩
  | cons p P ih =>
    have hn : (p.1 ≠ p.2 ∧ p.1 ∉ pairPorts P) ∧ p.2 ∉ pairPorts P ∧ (pairPorts P).Nodup := by
      simpa only [pairPorts_cons,List.nodup_cons,List.mem_cons,not_or] using hP
    have hma : m p.1 ≠ p.1 := ha _ (by simp [pairPorts_cons])
    have hmb : m p.2 ≠ p.2 := ha _ (by simp [pairPorts_cons])
    have hmi := splice_involutive m hm p.1 p.2 hn.1.1 hma hmb
    have hat : ∀ x ∈ pairPorts P, splice m p.1 p.2 x ≠ x := by
      intro x hx
      have hxa : x ≠ p.1 := fun h => hn.1.2 (h ▸ hx)
      have hxb : x ≠ p.2 := fun h => hn.2.1 (h ▸ hx)
      apply splice_active m hm p.1 p.2 x hn.1.1 hxa hxb
      exact ha x (by rw [pairPorts_cons]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
    have hi := ih (splice m p.1 p.2) hmi hn.2.2 hat
    refine ⟨hi.1,?_⟩
    intro x hx
    have ho : x ≠ p.1 ∧ x ≠ p.2 ∧ x ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hx
    exact (hi.2 x ho.2.2).trans (splice_fixed_iff m hm p.1 p.2 x hn.1.1 ho.1 ho.2.1)

end WaveTurbulence.Reg.Skeleton
