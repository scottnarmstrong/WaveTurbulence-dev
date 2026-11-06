/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SpliceFold

/-! # Literal splice transport along an injective matching-compatible port map -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem splice_naturality {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (m : α → α) (n : β → β) (hf : ∀ x, n (f x) = f (m x)) (a b x : α) :
    splice n (f a) (f b) (f x) = f (splice m a b x) := by
  by_cases hxa : x = a
  · subst x; simp
  by_cases hxb : x = b
  · subst x; simp
  by_cases hma : m x = a
  · simp [splice,f.injective.eq_iff,hxa,hxb,hf,hma]
  by_cases hmb : m x = b
  · by_cases hba : b = a <;> simp [splice,f.injective.eq_iff,hxa,hxb,hf,hmb,hba]
  · simp [splice,f.injective.eq_iff,hxa,hxb,hf,hma,hmb]

/-- A finite list of matched port removals transports exactly, including all original inactive slots. -/
theorem foldSplice_naturality {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α ↪ β) (P : List (α × α)) (m : α → α) (n : β → β)
    (hf : ∀ x, n (f x) = f (m x)) (x : α) :
    foldSplice n (P.map (fun p => (f p.1,f p.2))) (f x) = f (foldSplice m P x) := by
  induction P generalizing m n with
  | nil => exact hf x
  | cons p P ih =>
    exact ih (splice m p.1 p.2) (splice n (f p.1) (f p.2))
      (splice_naturality f m n hf p.1 p.2)

end WaveTurbulence.Reg.Skeleton
