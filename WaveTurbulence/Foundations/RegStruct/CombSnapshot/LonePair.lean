/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens

/-! # Extending an involution by one lone leaf (TARGET L637) -/

public section

namespace WaveTurbulence.Comb

variable {α : Type*} [DecidableEq α]

/-- Pair the complement of `lone` and fix `lone` itself. -/
@[expose] def pairWithLone (lone : α) (p : {a : α // a ≠ lone} → {a : α // a ≠ lone}) (a : α) : α :=
  if h : a = lone then lone else (p ⟨a, h⟩).1

/-- The distinguished leaf is fixed. -/
theorem pairWithLone_self (lone : α) (p : {a : α // a ≠ lone} → {a : α // a ≠ lone}) :
    pairWithLone lone p lone = lone := by simp [pairWithLone]

/-- On every other leaf the extension agrees with the given pairing. -/
theorem pairWithLone_other (lone : α) (p : {a : α // a ≠ lone} → {a : α // a ≠ lone})
    (a : {a : α // a ≠ lone}) : pairWithLone lone p a = (p a).1 := by
  simp [pairWithLone, a.2]

/-- An involution remains an involution after adding the lone leaf. -/
theorem pairWithLone_involutive (lone : α) (p : {a : α // a ≠ lone} → {a : α // a ≠ lone})
    (hp : Function.Involutive p) : Function.Involutive (pairWithLone lone p) := by
  intro a
  by_cases ha : a = lone
  · subst a
    rw [pairWithLone_self, pairWithLone_self]
  · let x : {a : α // a ≠ lone} := ⟨a, ha⟩
    change pairWithLone lone p (pairWithLone lone p x.1) = x.1
    rw [pairWithLone_other, pairWithLone_other, hp x]

/-- No new fixed point appears outside the lone leaf. -/
theorem pairWithLone_eq_iff (lone : α) (p : {a : α // a ≠ lone} → {a : α // a ≠ lone})
    (hp : ∀ x, p x ≠ x) (a : α) : pairWithLone lone p a = a ↔ a = lone := by
  by_cases ha : a = lone
  · subst a
    simp [pairWithLone_self]
  · constructor
    · intro h
      have he : p ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext (by simpa [pairWithLone, ha] using h)
      exact (hp _ he).elim
    · exact fun h => (ha h).elim

/-- A complement pairing respecting the sign rule gives a paired tree. -/
@[expose] def pairedTreeWithLone (t : TTree) (ζ : ℤˣ)
    (lone : GLeaf (fun _ : Fin 1 => t))
    (p : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone} → {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone})
    (hp : Function.Involutive p) (hn : ∀ ℓ, p ℓ ≠ ℓ)
    (hs : ∀ ℓ, nodeSign (fun _ : Fin 1 => ζ) (p ℓ).1.1 =
      -nodeSign (fun _ : Fin 1 => ζ) ℓ.1.1) : Garden 1 where
  sig _ := ζ
  tree _ := t
  pair := pairWithLone lone p
  mark ℓ := if ℓ = lone then some MarkTag.lower else none
  pair_pair := pairWithLone_involutive lone p hp
  pair_eq_iff := by
    intro ℓ
    rw [pairWithLone_eq_iff lone p hn ℓ]
    by_cases h : ℓ = lone <;> simp [h]
  pair_sign := by
    intro ℓ hne
    have hℓ : ℓ ≠ lone := by
      intro he
      subst ℓ
      exact hne (pairWithLone_self lone p)
    rw [show pairWithLone lone p ℓ = (p ⟨ℓ, hℓ⟩).1 from pairWithLone_other lone p ⟨ℓ, hℓ⟩]
    exact hs ⟨ℓ, hℓ⟩

/-- The construction has exactly one marked leaf, tagged `lower`. -/
theorem pairedTreeWithLone_isPairedTree (t : TTree) (ζ : ℤˣ)
    (lone : GLeaf (fun _ : Fin 1 => t))
    (p : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone} → {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone})
    (hp : Function.Involutive p) (hn : ∀ ℓ, p ℓ ≠ ℓ)
    (hs : ∀ ℓ, nodeSign (fun _ : Fin 1 => ζ) (p ℓ).1.1 =
      -nodeSign (fun _ : Fin 1 => ζ) ℓ.1.1) :
    IsPairedTree (pairedTreeWithLone t ζ lone p hp hn hs) := by
  classical
  constructor
  · change (Finset.univ.filter (fun ℓ => (if ℓ = lone then some MarkTag.lower else none) ≠ none)).card = 1
    have he : (Finset.univ.filter (fun ℓ : GLeaf (fun _ : Fin 1 => t) =>
        (if ℓ = lone then some MarkTag.lower else none) ≠ none)) = {lone} := by
      ext ℓ
      by_cases h : ℓ = lone <;> simp [h]
    rw [he]
    rfl
  · intro ℓ hℓ
    dsimp only [pairedTreeWithLone] at hℓ
    dsimp only [Garden.IsLone, pairedTreeWithLone]
    split_ifs with he
    · rfl
    · exact (hℓ (ite_eq_right he)).elim

end WaveTurbulence.Comb
