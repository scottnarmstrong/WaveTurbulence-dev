/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Gardens

/-! # Transporting a pairing to a closed leaf embedding

Infrastructure for components and embedded objects in TARGET L636, L845–L847.
The leaf embedding is injective and its image is closed under the original
pairing. These structural data determine the transported pairing uniquely.
-/

public section

namespace WaveTurbulence.Comb

variable {w v : ℕ} {G : Garden w} {tree : Fin v → TTree}

/-- Pull back a pairing along an injective, pairing-closed leaf map. -/
@[expose] noncomputable def leafPairPullback (f : GLeaf tree ↪ GLeaf G.tree)
    (hc : ∀ ℓ, ∃ ℓ', f ℓ' = G.pair (f ℓ)) (ℓ : GLeaf tree) : GLeaf tree :=
  Classical.choose (hc ℓ)

/-- The pulled-back pairing commutes with the actual ambient pairing. -/
theorem leafPairPullback_spec (f : GLeaf tree ↪ GLeaf G.tree)
    (hc : ∀ ℓ, ∃ ℓ', f ℓ' = G.pair (f ℓ)) (ℓ : GLeaf tree) :
    f (leafPairPullback f hc ℓ) = G.pair (f ℓ) := Classical.choose_spec (hc ℓ)

/-- Injectivity makes the pulled-back partner unique. -/
theorem leafPairPullback_unique (f : GLeaf tree ↪ GLeaf G.tree)
    (hc : ∀ ℓ, ∃ ℓ', f ℓ' = G.pair (f ℓ)) {ℓ ℓ' : GLeaf tree}
    (h : f ℓ' = G.pair (f ℓ)) : ℓ' = leafPairPullback f hc ℓ :=
  f.injective (h.trans (leafPairPullback_spec f hc ℓ).symm)

/-- Build a garden on a leaf embedding whose image is closed under pairing.
Sign preservation is literal equality of the node signs at the embedded leaves. -/
@[expose] noncomputable def gardenOnLeafEmbedding (sig : Fin v → ℤˣ)
    (f : GLeaf tree ↪ GLeaf G.tree) (hc : ∀ ℓ, ∃ ℓ', f ℓ' = G.pair (f ℓ))
    (hs : ∀ ℓ, nodeSign sig ℓ.1 = nodeSign G.sig (f ℓ).1) : Garden v where
  sig := sig
  tree := tree
  pair := leafPairPullback f hc
  mark ℓ := G.mark (f ℓ)
  pair_pair := by
    intro ℓ
    apply f.injective
    rw [leafPairPullback_spec, leafPairPullback_spec, G.pair_pair]
  pair_eq_iff := by
    intro ℓ
    have he : leafPairPullback f hc ℓ = ℓ ↔ G.pair (f ℓ) = f ℓ := by
      rw [← leafPairPullback_spec f hc ℓ]
      exact f.injective.eq_iff.symm
    exact he.trans (G.pair_eq_iff (f ℓ))
  pair_sign := by
    intro ℓ hne
    have ho : G.pair (f ℓ) ≠ f ℓ := by
      intro he
      apply hne
      exact f.injective ((leafPairPullback_spec f hc ℓ).trans he)
    calc nodeSign sig (leafPairPullback f hc ℓ).1 =
        nodeSign G.sig (f (leafPairPullback f hc ℓ)).1 := hs _
      _ = nodeSign G.sig (G.pair (f ℓ)).1 :=
        congrArg (fun a : GLeaf G.tree => nodeSign G.sig a.1) (leafPairPullback_spec f hc ℓ)
      _ = -nodeSign G.sig (f ℓ).1 := G.pair_sign (f ℓ) ho
      _ = -nodeSign sig ℓ.1 := congrArg Neg.neg (hs ℓ).symm

/-- Restricting a plain pairing-closed garden produces a plain garden. -/
theorem gardenOnLeafEmbedding_plain (sig : Fin v → ℤˣ)
    (f : GLeaf tree ↪ GLeaf G.tree) (hc : ∀ ℓ, ∃ ℓ', f ℓ' = G.pair (f ℓ))
    (hs : ∀ ℓ, nodeSign sig ℓ.1 = nodeSign G.sig (f ℓ).1) (hG : G.IsPlain) :
    (gardenOnLeafEmbedding sig f hc hs).IsPlain := fun ℓ => hG (f ℓ)

end WaveTurbulence.Comb
