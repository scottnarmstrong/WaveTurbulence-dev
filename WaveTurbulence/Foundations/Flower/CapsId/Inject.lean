/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Garden
/-! # A2 CAPS-ID: capping is injective on flower gardens (supplement Lemma 2.1(4), inverse direction)

A flower garden is recovered from its capped garden: trees, signs and layers by restriction, the pairing of
non-flowers by restriction, and the flowers as the leaves paired with a cap. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7

variable {w : ℕ}

/-- On a flower garden the marks are determined by the flowers. -/
theorem mark_eq_of_isFlowerGarden {G : Garden w} (hG : G.IsFlowerGarden) (ℓ : GLeaf G.tree) :
    G.mark ℓ = if G.IsFlower ℓ then some MarkTag.equal else none := by
  by_cases hf : G.IsFlower ℓ
  · rw [ite_eq_left hf]; exact hf
  · rw [ite_eq_right hf]
    by_contra hm
    exact hf (hG.2.1 ℓ hm)

/-- **Lemma 2.1(4)**: `capLayered · p` is injective on flower gardens. -/
theorem capLayered_injective (p : ℕ) {LG₁ LG₂ : LayeredGarden w} (h₁ : LG₁.garden.IsFlowerGarden)
    (h₂ : LG₂.garden.IsFlowerGarden) (h : capLayered LG₁ p = capLayered LG₂ p) : LG₁ = LG₂ := by
  obtain ⟨⟨sig₁, T₁, pair₁, mark₁, pp₁, pe₁, ps₁⟩, lay₁, il₁⟩ := LG₁
  obtain ⟨⟨sig₂, T₂, pair₂, mark₂, pp₂, pe₂, ps₂⟩, lay₂, il₂⟩ := LG₂
  have hT : T₁ = T₂ := funext fun j => by
    have := congrArg (fun L : LayeredGarden (2 * w) => L.garden.tree (capσ w (.inl j))) h
    simpa only [capGarden_tree_inl] using this
  subst hT
  have hs : sig₁ = sig₂ := funext fun j => by
    have := congrArg (fun L : LayeredGarden (2 * w) => L.garden.sig (capσ w (.inl j))) h
    simpa only [capGarden_sig_inl] using this
  subst hs
  have hlayH := congr_arg_heq LayeredGarden.layer h
  have hl : lay₁ = lay₂ := funext fun a => by
    have e := congrFun (eq_of_heq hlayH) (embN _ a)
    have e₁ := capLayer_embN (⟨⟨sig₁, T₁, pair₁, mark₁, pp₁, pe₁, ps₁⟩, lay₁, il₁⟩ : LayeredGarden w) p a
    have e₂ := capLayer_embN (⟨⟨sig₁, T₁, pair₂, mark₂, pp₂, pe₂, ps₂⟩, lay₂, il₂⟩ : LayeredGarden w) p a
    exact e₁.symm.trans (e.trans e₂)
  subst hl
  set G₁ : Garden w := ⟨sig₁, T₁, pair₁, mark₁, pp₁, pe₁, ps₁⟩
  set G₂ : Garden w := ⟨sig₁, T₁, pair₂, mark₂, pp₂, pe₂, ps₂⟩
  have hF₁ : OneFlower G₁ := oneFlower_of_isFlowerGarden h₁
  have hF₂ : OneFlower G₂ := oneFlower_of_isFlowerGarden h₂
  have hg : capGarden G₁ = capGarden G₂ := congrArg LayeredGarden.garden h
  have hpairH := congr_arg_heq Garden.pair hg
  have hpair : ∀ x : GLeaf (capGarden G₁).tree, (capGarden G₁).pair x = (capGarden G₂).pair x :=
    fun x => congrFun (eq_of_heq hpairH) x
  -- flowers and pairs agree
  have key : ∀ ℓ : GLeaf T₁, (G₁.IsFlower ℓ ↔ G₂.IsFlower ℓ) ∧ pair₁ ℓ = pair₂ ℓ := by
    intro ℓ
    have e := hpair (embL G₁ ℓ)
    have e₁ := capGarden_pair_embL G₁ ℓ
    have e₂ : (capGarden G₂).pair (embL G₁ ℓ) = _ := capGarden_pair_embL G₂ ℓ
    by_cases f₁ : G₁.IsFlower ℓ <;> by_cases f₂ : G₂.IsFlower ℓ
    · refine ⟨iff_of_true f₁ f₂, ?_⟩
      have m₁ : mark₁ ℓ ≠ none := by
        change G₁.mark ℓ ≠ none; unfold Garden.IsFlower at f₁; rw [f₁]; exact Option.some_ne_none _
      have m₂ : mark₂ ℓ ≠ none := by
        change G₂.mark ℓ ≠ none; unfold Garden.IsFlower at f₂; rw [f₂]; exact Option.some_ne_none _
      exact ((pe₁ ℓ).2 m₁).trans ((pe₂ ℓ).2 m₂).symm
    · exfalso
      rw [ite_eq_left ((flowerOf_self_iff hF₁ ℓ).2 f₁)] at e₁
      rw [ite_eq_right (fun hc => f₂ ((flowerOf_self_iff hF₂ ℓ).1 hc))] at e₂
      exact embL_ne_capL G₁ (pair₂ ℓ) ℓ.1.1 ((e₂.symm.trans e.symm).trans e₁)
    · exfalso
      rw [ite_eq_right (fun hc => f₁ ((flowerOf_self_iff hF₁ ℓ).1 hc))] at e₁
      rw [ite_eq_left ((flowerOf_self_iff hF₂ ℓ).2 f₂)] at e₂
      exact embL_ne_capL G₁ (pair₁ ℓ) ℓ.1.1 ((e₁.symm.trans e).trans e₂)
    · refine ⟨iff_of_false f₁ f₂, ?_⟩
      rw [ite_eq_right (fun hc => f₁ ((flowerOf_self_iff hF₁ ℓ).1 hc))] at e₁
      rw [ite_eq_right (fun hc => f₂ ((flowerOf_self_iff hF₂ ℓ).1 hc))] at e₂
      exact embL_injective G₁ ((e₁.symm.trans e).trans e₂)
  have hp : pair₁ = pair₂ := funext fun ℓ => (key ℓ).2
  have hm : mark₁ = mark₂ := funext fun ℓ => by
    have a₁ := mark_eq_of_isFlowerGarden h₁ ℓ
    have a₂ := mark_eq_of_isFlowerGarden h₂ ℓ
    change G₁.mark ℓ = G₂.mark ℓ
    rw [a₁, a₂]
    by_cases f₁ : G₁.IsFlower ℓ
    · rw [ite_eq_left f₁, ite_eq_left ((key ℓ).1.1 f₁)]
    · rw [ite_eq_right f₁, ite_eq_right (fun f₂ => f₁ ((key ℓ).1.2 f₂))]
  subst hp hm
  rfl

end WaveTurbulence.Flower.CapsId
