/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.LonePair

/-! # Restricting pairings to complements of lone leaves (TARGET L637, L846) -/

public section

namespace WaveTurbulence.Comb

variable {w : ℕ} {G : Garden w} {α : Type*}

/-- Pull the ambient pairing back to any injective, pairing-closed index type. -/
@[expose] noncomputable def partnerPullback (f : α ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (x : α) : α := Classical.choose (hc x)

theorem partnerPullback_spec (f : α ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (x : α) :
    f (partnerPullback f hc x) = G.pair (f x) := Classical.choose_spec (hc x)

theorem partnerPullback_involutive (f : α ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) : Function.Involutive (partnerPullback f hc) := by
  intro x
  apply f.injective
  rw [partnerPullback_spec, partnerPullback_spec, G.pair_pair]

theorem partnerPullback_ne (f : α ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (hn : ∀ x, G.pair (f x) ≠ f x) (x : α) :
    partnerPullback f hc x ≠ x := by
  intro h
  exact hn x ((partnerPullback_spec f hc x).symm.trans (congrArg f h))

/-- The sign-reversing pairing transports to the non-lone leaves. -/
theorem partnerPullback_sign (t : TTree) (ζ : ℤˣ) (lone : GLeaf (fun _ : Fin 1 => t))
    (f : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone} ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (hn : ∀ x, G.pair (f x) ≠ f x)
    (hs : ∀ x, nodeSign (fun _ : Fin 1 => ζ) x.1.1 = nodeSign G.sig (f x).1)
    (x : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone}) :
    nodeSign (fun _ : Fin 1 => ζ) (partnerPullback f hc x).1.1 =
      -nodeSign (fun _ : Fin 1 => ζ) x.1.1 := by
  rw [hs, partnerPullback_spec, G.pair_sign (f x) (hn x), hs]

/-- A closed embedding of all non-lone leaves constructs the actual paired tree. -/
@[expose] noncomputable def pairedTreeFromLeafEmbedding
    (t : TTree) (ζ : ℤˣ) (lone : GLeaf (fun _ : Fin 1 => t))
    (f : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone} ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (hn : ∀ x, G.pair (f x) ≠ f x)
    (hs : ∀ x, nodeSign (fun _ : Fin 1 => ζ) x.1.1 = nodeSign G.sig (f x).1) : Garden 1 :=
  pairedTreeWithLone t ζ lone (partnerPullback f hc) (partnerPullback_involutive f hc)
    (partnerPullback_ne f hc hn) (partnerPullback_sign t ζ lone f hc hn hs)

theorem pairedTreeFromLeafEmbedding_isPairedTree
    (t : TTree) (ζ : ℤˣ) (lone : GLeaf (fun _ : Fin 1 => t))
    (f : {ℓ : GLeaf (fun _ : Fin 1 => t) // ℓ ≠ lone} ↪ GLeaf G.tree)
    (hc : ∀ x, ∃ y, f y = G.pair (f x)) (hn : ∀ x, G.pair (f x) ≠ f x)
    (hs : ∀ x, nodeSign (fun _ : Fin 1 => ζ) x.1.1 = nodeSign G.sig (f x).1) :
    IsPairedTree (pairedTreeFromLeafEmbedding t ζ lone f hc hn hs) :=
  pairedTreeWithLone_isPairedTree _ _ _ _ _ _ _

end WaveTurbulence.Comb
