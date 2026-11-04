/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens

/-! # Leaf pairing data for surgery (TARGET L632, L846–L847)

This helper separates a literal signed involution from the addresses carrying
it. It allows disjoint leaf families to be assembled without changing the
frozen garden carrier.
-/

public section

namespace WaveTurbulence.Comb

/-- A signed involution with exactly the marked elements as fixed points. -/
structure SignedPairing (α : Type*) where
  sign : α → ℤˣ
  pair : α → α
  mark : α → Option MarkTag
  pair_pair : ∀ a, pair (pair a) = a
  pair_eq_iff : ∀ a, pair a = a ↔ mark a ≠ none
  pair_sign : ∀ a, pair a ≠ a → sign (pair a) = -sign a

/-- The literal pairing carried by a garden. -/
@[expose] def gardenPairing {w : ℕ} (G : Garden w) : SignedPairing (GLeaf G.tree) where
  sign ℓ := nodeSign G.sig ℓ.1
  pair := G.pair
  mark := G.mark
  pair_pair := G.pair_pair
  pair_eq_iff := G.pair_eq_iff
  pair_sign := G.pair_sign

/-- Disjoint sum of two signed pairings. -/
@[expose] def SignedPairing.sum {α β : Type*} (P : SignedPairing α) (Q : SignedPairing β) :
    SignedPairing (α ⊕ β) where
  sign := Sum.elim P.sign Q.sign
  pair := Sum.map P.pair Q.pair
  mark := Sum.elim P.mark Q.mark
  pair_pair a := by cases a <;> simp [P.pair_pair, Q.pair_pair]
  pair_eq_iff a := by cases a <;> simp [P.pair_eq_iff, Q.pair_eq_iff]
  pair_sign a h := by
    cases a with
    | inl a => exact P.pair_sign a (fun he => h (congrArg Sum.inl he))
    | inr a => exact Q.pair_sign a (fun he => h (congrArg Sum.inr he))

/-- Restrict to a family closed under the involution. -/
@[expose] def SignedPairing.subtype {α : Type*} (P : SignedPairing α) (S : α → Prop)
    (hS : ∀ a, S a → S (P.pair a)) : SignedPairing {a : α // S a} where
  sign a := P.sign a.1
  pair a := ⟨P.pair a.1, hS a.1 a.2⟩
  mark a := P.mark a.1
  pair_pair a := Subtype.ext (P.pair_pair a.1)
  pair_eq_iff a := by
    rw [Subtype.ext_iff]
    exact P.pair_eq_iff _
  pair_sign a h := P.pair_sign a.1 (fun he => h (Subtype.ext he))

/-- Move literal leaf pairing data through a bijection onto the new leaf set. -/
@[expose] def gardenFromLeafEquiv {α : Type*} {w : ℕ} (tree : Fin w → TTree) (sig : Fin w → ℤˣ)
    (P : SignedPairing α) (e : GLeaf tree ≃ α)
    (hs : ∀ ℓ, nodeSign sig ℓ.1 = P.sign (e ℓ)) : Garden w where
  tree := tree
  sig := sig
  pair ℓ := e.symm (P.pair (e ℓ))
  mark ℓ := P.mark (e ℓ)
  pair_pair ℓ := by simp only [Equiv.apply_symm_apply, P.pair_pair, Equiv.symm_apply_apply]
  pair_eq_iff ℓ := by
    rw [Equiv.symm_apply_eq]
    exact P.pair_eq_iff _
  pair_sign ℓ h := by
    have hp : P.pair (e ℓ) ≠ e ℓ := fun he => h (by rw [he, Equiv.symm_apply_apply])
    calc nodeSign sig (e.symm (P.pair (e ℓ))).1 = P.sign (e (e.symm (P.pair (e ℓ)))) := hs _
      _ = P.sign (P.pair (e ℓ)) := by rw [Equiv.apply_symm_apply]
      _ = -P.sign (e ℓ) := P.pair_sign _ hp
      _ = -nodeSign sig ℓ.1 := congrArg Neg.neg (hs ℓ).symm

/-- The constructed garden's pairing commutes with the specified leaf bijection. -/
theorem gardenFromLeafEquiv_pair {α : Type*} {w : ℕ} (tree : Fin w → TTree) (sig : Fin w → ℤˣ)
    (P : SignedPairing α) (e : GLeaf tree ≃ α) (hs : ∀ ℓ, nodeSign sig ℓ.1 = P.sign (e ℓ))
    (ℓ : GLeaf tree) : e ((gardenFromLeafEquiv tree sig P e hs).pair ℓ) = P.pair (e ℓ) :=
  e.apply_symm_apply _

end WaveTurbulence.Comb
