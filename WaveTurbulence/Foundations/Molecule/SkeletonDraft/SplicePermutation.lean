/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceFold

/-! # Disjoint active-port deletion does not depend on its enumeration -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem pairPorts_nodup_cons {α : Type*} (p : α × α) (P : List (α × α)) :
    (pairPorts (p::P)).Nodup ↔ p.1 ≠ p.2 ∧ p.1 ∉ pairPorts P ∧ p.2 ∉ pairPorts P ∧ (pairPorts P).Nodup := by
  simp only [pairPorts_cons,List.nodup_cons,List.mem_cons,not_or,and_assoc]

theorem pairPorts_perm {α : Type*} {P Q : List (α × α)} (h : P.Perm Q) :
    (pairPorts P).Perm (pairPorts Q) := h.flatMap_right _

/-- The head splice retains activity of every as-yet-undeleted target. -/
theorem splice_tail_active {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (p : α × α) (P : List (α × α))
    (hn : (pairPorts (p::P)).Nodup) (ha : ∀ x ∈ pairPorts (p::P), m x ≠ x) :
    ∀ x ∈ pairPorts P, splice m p.1 p.2 x ≠ x := by
  have ht := pairPorts_nodup_cons p P |>.mp hn
  intro x hx
  have hxa : x ≠ p.1 := fun h => ht.2.1 (h ▸ hx)
  have hxb : x ≠ p.2 := fun h => ht.2.2.1 (h ▸ hx)
  apply splice_active m hm p.1 p.2 x ht.1 hxa hxb
  exact ha x (by rw [pairPorts_cons]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))

/-- Any permutation of a disjoint active-port splice list gives the same matching. -/
theorem foldSplice_perm {α : Type*} [DecidableEq α] {P Q : List (α × α)} (h : P.Perm Q) :
    ∀ (m : α → α), Function.Involutive m → (pairPorts P).Nodup →
      (∀ x ∈ pairPorts P, m x ≠ x) → foldSplice m P = foldSplice m Q := by
  induction h with
  | nil => intro m _ _ _; rfl
  | @cons p P Q h ih =>
    intro m hm hn ha
    have ht := (pairPorts_nodup_cons p P).mp hn
    have hma : m p.1 ≠ p.1 := ha _ (by simp [pairPorts_cons])
    have hmb : m p.2 ≠ p.2 := ha _ (by simp [pairPorts_cons])
    exact ih (splice m p.1 p.2) (splice_involutive m hm p.1 p.2 ht.1 hma hmb)
      ht.2.2.2 (splice_tail_active m hm p P hn ha)
  | swap p q P =>
    intro m hm hn _
    have hq := (pairPorts_nodup_cons q (p::P)).mp hn
    have hp := (pairPorts_nodup_cons p P).mp hq.2.2.2
    have h1 : q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.1 ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hq.2.1
    have h2 : q.2 ≠ p.1 ∧ q.2 ≠ p.2 ∧ q.2 ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hq.2.2.1
    exact congrArg (fun f => foldSplice f P)
      (splice_commute m hm q.1 q.2 p.1 p.2 hq.1 h1.1 h1.2.1 h2.1 h2.2.1 hp.1)
  | @trans P Q R hPQ hQR ihPQ ihQR =>
    intro m hm hn ha
    have hp := pairPorts_perm hPQ
    have hqn : (pairPorts Q).Nodup := hp.nodup_iff.mp hn
    have hqa : ∀ x ∈ pairPorts Q, m x ≠ x := fun x hx => ha x (hp.mem_iff.mpr hx)
    exact (ihPQ m hm hn ha).trans (ihQR m hm hqn hqa)

end WaveTurbulence.Reg.Skeleton
