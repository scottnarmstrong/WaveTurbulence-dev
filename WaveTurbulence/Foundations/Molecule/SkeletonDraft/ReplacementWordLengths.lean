/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReplacementWords

/-! # A single linear description bound for all reconstruction slots -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem chainWords_length (X : List RegChain) (hw : ∀ x ∈ X, x.wf = true) :
    (X.flatMap chainWord).length ≤ 4 * (X.map RegChain.size).sum + X.length := by
  induction X with
  | nil => simp
  | cons x X ih =>
    have hx := (chainWord_length x (hw x (by simp))).1
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,List.length_cons]
    omega

theorem coupleWords_length (Q : List RegCpl) (hw : ∀ q ∈ Q, q.wf = true) :
    (Q.flatMap coupleWord).length ≤ 4 * (Q.map RegCpl.size).sum + Q.length := by
  induction Q with
  | nil => simp
  | cons q Q ih =>
    have hq := coupleWord_length q (hw q (by simp))
    have ht := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,List.length_cons]
    omega

/-- The description cost is four per added branch plus one per fixed replacement slot. -/
theorem replacementWord_length {n q : ℕ} (X : Fin n → RegChain) (Q : Fin q → RegCpl)
    (hX : ∀ i, (X i).wf = true) (hQ : ∀ i, (Q i).wf = true) :
    (replacementWord X Q).length ≤ 4 * ((∑ i, (X i).size) + ∑ i, (Q i).size) + n + q := by
  have hx := chainWords_length (List.ofFn X) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hX i)
  have hq := coupleWords_length (List.ofFn Q) (by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact hQ i)
  simp only [List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn] at hx hq
  change ((List.ofFn X).flatMap chainWord ++ (List.ofFn Q).flatMap coupleWord).length ≤ _
  rw [List.length_append]
  omega

end WaveTurbulence.Reg.Skeleton
