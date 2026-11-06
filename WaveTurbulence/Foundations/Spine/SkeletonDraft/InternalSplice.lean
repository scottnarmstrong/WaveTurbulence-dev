/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SplicePermutation

/-! # Deleting matched internal edges leaves every other edge unchanged -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- An already matched splice only deactivates its two endpoints. -/
theorem splice_matched {α : Type*} [DecidableEq α] (m : α → α)
    (hm : Function.Involutive m) (a b : α) (hab : m a = b) (x : α) :
    splice m a b x = if x = a ∨ x = b then x else m x := by
  by_cases hx : x = a ∨ x = b
  · simp [splice,hx]
  · have hxa := (not_or.mp hx).1
    have hxb := (not_or.mp hx).2
    have hba : m b = a := by rw [← hab,hm a]
    have hma : m x ≠ a := by
      intro he
      have he' := congrArg m he
      rw [hm x,hab] at he'
      exact hxb he'
    have hmb : m x ≠ b := fun he => hxa (hm.injective (he.trans hab.symm))
    simp [splice,hx,hma,hmb]

/-- Removing pairwise disjoint already matched edges preserves every remaining edge. -/
theorem foldSplice_matched {α : Type*} [DecidableEq α] (P : List (α × α))
    (m : α → α) (hm : Function.Involutive m) (hn : (pairPorts P).Nodup)
    (hP : ∀ p ∈ P, m p.1 = p.2) (x : α) (hx : x ∉ pairPorts P) :
    foldSplice m P x = m x := by
  induction P generalizing m with
  | nil => rfl
  | cons p P ih =>
    obtain ⟨hab,hap,hbp,hn'⟩ := (pairPorts_nodup_cons p P).mp hn
    have hx' : x ≠ p.1 ∧ x ≠ p.2 ∧ x ∉ pairPorts P := by
      simpa only [pairPorts_cons,List.mem_cons,not_or] using hx
    have hp := hP p (List.mem_cons_self)
    have hactiveA : m p.1 ≠ p.1 := by rw [hp]; exact Ne.symm hab
    have hactiveB : m p.2 ≠ p.2 := by
      have he : m p.2 = p.1 := by rw [← hp,hm p.1]
      rw [he]
      exact hab
    change foldSplice (splice m p.1 p.2) P x = m x
    rw [ih (splice m p.1 p.2) (splice_involutive m hm _ _ hab hactiveA hactiveB) hn' ?_ hx'.2.2]
    · rw [splice_matched m hm _ _ hp,ite_eq_right (not_or.mpr ⟨hx'.1,hx'.2.1⟩)]
    · intro q hq
      have hqA : q.1 ≠ p.1 := fun he => hap (by rw [← he]; exact List.mem_flatMap.mpr ⟨q,hq,by simp⟩)
      have hqB : q.1 ≠ p.2 := fun he => hbp (by rw [← he]; exact List.mem_flatMap.mpr ⟨q,hq,by simp⟩)
      rw [splice_matched m hm _ _ hp,ite_eq_right (not_or.mpr ⟨hqA,hqB⟩)]
      exact hP q (List.mem_cons_of_mem _ hq)

end WaveTurbulence.Reg.Skeleton
