/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionCounts
import Mathlib.Tactic

/-! # Every fresh atom belongs to one literal slot allocation interval -/

public section
namespace WaveTurbulence.Vine

/-- The successive insertion intervals partition the new atom range.
This statement concerns the literal allocation arithmetic, not selected masks. -/
theorem fold_fresh_allocation (T : VineTemplate)
    (xs : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (i : ℕ) (hi : T.n ≤ i)
    (hin : i<(xs.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n) :
    ∃ pre post s k,xs=pre++(s,k)::post ∧
      (pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n ≤ i ∧
      i<(pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T).n+2*k := by
  induction xs generalizing T with
  | nil => simp only [List.foldl_nil] at hin; omega
  | cons sk xs ih =>
    by_cases hfirst : i<T.n+2*sk.2
    · exact ⟨[],xs,sk.1,sk.2,rfl,hi,hfirst⟩
    · have hlo : (insertRungs T sk.1 sk.2).n ≤ i := by rw [insertRungs_atoms]; omega
      obtain ⟨pre,post,s,k,he,hlo,hhi⟩ := ih (insertRungs T sk.1 sk.2) hlo hin
      refine ⟨sk::pre,post,s,k,?_,hlo,hhi⟩
      simpa only [List.cons_append] using congrArg (List.cons sk) he

end WaveTurbulence.Vine
