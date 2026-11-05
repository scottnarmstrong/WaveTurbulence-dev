/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionData

/-! # Joint prefix encoding of all regular replacement slots -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

/-- Prefix parsing of a fixed number of regular trees leaves the exact unused suffix. -/
theorem chainWords_prefix (X Y : List RegChain) (a b : List (Fin 11))
    (hlen : X.length = Y.length)
    (he : X.flatMap chainWord ++ a = Y.flatMap chainWord ++ b) : X = Y ∧ a = b := by
  induction X generalizing Y a b with
  | nil =>
    have hy : Y = [] := List.length_eq_zero_iff.mp hlen.symm
    subst Y
    exact ⟨rfl,he⟩
  | cons x X ih =>
    cases Y with
    | nil => simp at hlen
    | cons y Y =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      simp only [List.flatMap_cons,List.append_assoc] at he
      obtain ⟨hxy,ht⟩ := chainWord_prefix x y _ _ he
      obtain ⟨hXY,hab⟩ := ih Y a b hlen ht
      exact ⟨congrArg₂ List.cons hxy hXY,hab⟩

/-- Prefix parsing of a fixed number of regular couples leaves the exact unused suffix. -/
theorem coupleWords_prefix (X Y : List RegCpl) (a b : List (Fin 11))
    (hlen : X.length = Y.length)
    (he : X.flatMap coupleWord ++ a = Y.flatMap coupleWord ++ b) : X = Y ∧ a = b := by
  induction X generalizing Y a b with
  | nil =>
    have hy : Y = [] := List.length_eq_zero_iff.mp hlen.symm
    subst Y
    exact ⟨rfl,he⟩
  | cons x X ih =>
    cases Y with
    | nil => simp at hlen
    | cons y Y =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at hlen
      simp only [List.flatMap_cons,List.append_assoc] at he
      obtain ⟨hxy,ht⟩ := coupleWord_prefix x y _ _ he
      obtain ⟨hXY,hab⟩ := ih Y a b hlen ht
      exact ⟨congrArg₂ List.cons hxy hXY,hab⟩

/-- All regular trees followed by all regular couples, using their existing self-delimiting words. -/
def replacementWord {n q : ℕ} (X : Fin n → RegChain) (Q : Fin q → RegCpl) : List (Fin 11) :=
  (List.ofFn X).flatMap chainWord ++ (List.ofFn Q).flatMap coupleWord

/-- No separators or individual size compositions are needed to recover any replacement slot. -/
theorem replacementWord_injective {n q : ℕ} (X Y : Fin n → RegChain) (Q R : Fin q → RegCpl)
    (he : replacementWord X Q = replacementWord Y R) : X = Y ∧ Q = R := by
  obtain ⟨hXY,hQR⟩ := chainWords_prefix (List.ofFn X) (List.ofFn Y) _ _
    (by simp) he
  have hQR' : (List.ofFn Q).flatMap coupleWord ++ [] = (List.ofFn R).flatMap coupleWord ++ [] := by
    simpa only [List.append_nil] using hQR
  have hh := coupleWords_prefix (List.ofFn Q) (List.ofFn R) [] [] (by simp) hQR'
  exact ⟨List.ofFn_injective hXY,List.ofFn_injective hh.1⟩

end WaveTurbulence.Reg.Skeleton
