/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SplicePermutation
public import Mathlib.Data.List.FinRange

/-! # Reindexing and reversing the enumerated port-deletion pairs -/

public section
namespace WaveTurbulence.Reg.Skeleton

/-- Reindexing a finite tuple permutes its literal list of entries. -/
theorem ofFn_perm_equiv {α : Type*} {n : ℕ} (e : Equiv.Perm (Fin n)) (f : Fin n → α) :
    (List.ofFn (fun i => f (e i))).Perm (List.ofFn f) := by
  have hp : (List.ofFn e).Perm (List.ofFn (fun i : Fin n => i)) := by
    apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr e.injective)
      (List.nodup_ofFn.mpr Function.injective_id)).mpr
    intro i
    simp only [List.mem_ofFn]
    constructor
    · intro _; exact ⟨i,rfl⟩
    · intro _; exact ⟨e.symm i,e.apply_symm_apply i⟩
  simpa only [List.map_ofFn,Function.comp_def] using hp.map f

/-- Reversing the endpoints of every deletion pair changes no splice. -/
theorem foldSplice_map_swap {α : Type*} [DecidableEq α] (P : List (α × α)) (m : α → α) :
    foldSplice m (P.map Prod.swap) = foldSplice m P := by
  induction P generalizing m with
  | nil => rfl
  | cons p P ih =>
    change foldSplice (splice m p.2 p.1) (P.map Prod.swap) = foldSplice (splice m p.1 p.2) P
    rw [splice_symm m p.2 p.1]
    exact ih _

end WaveTurbulence.Reg.Skeleton
