/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceApp

public import WaveTurbulence.Foundations.XChain.SNormAddBounds

public import WaveTurbulence.Foundations.Spine.InputLeafCount

public import WaveTurbulence.Foundations.RegStruct.CodeOrders

public import WaveTurbulence.Foundations.Spine.CoherentConjugacyData

public import WaveTurbulence.Foundations.Spine.PL234Draft.CoherentTaylor

public import WaveTurbulence.Foundations.Spine.PL234Draft.TreeInduction
public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-!
# A code determines its decoded carrier

* `garden_ext`: gardens with the same signs, trees, partners and marks are equal;
* `decodes_unique`: two couple carriers of one code are equal (REG-STRUCT's decoded pair relation is functional);
* `decodesTree_unique`: two tree carriers of one chain code with the same root sign are equal;
* `layeredGarden_ext`;
* **`coherentCouple_unique`**, **`coherentTree_unique`**: a coherent object with equal parent layers `q = q'` has
  exactly one coherent carrier (its decoded garden, every node in layer `q`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Links

theorem garden_ext {w : ℕ} {G₁ G₂ : Garden w} (hs : G₁.sig = G₂.sig) (ht : G₁.tree = G₂.tree)
    (hp : ∀ (ℓ₁ : GLeaf G₁.tree) (ℓ₂ : GLeaf G₂.tree), ℓ₁.1 = ℓ₂.1 → (G₁.pair ℓ₁).1 = (G₂.pair ℓ₂).1)
    (hm : ∀ (ℓ₁ : GLeaf G₁.tree) (ℓ₂ : GLeaf G₂.tree), ℓ₁.1 = ℓ₂.1 → G₁.mark ℓ₁ = G₂.mark ℓ₂) : G₁ = G₂ := by
  obtain ⟨s₁, t₁, p₁, m₁, _, _, _⟩ := G₁
  obtain ⟨s₂, t₂, p₂, m₂, _, _, _⟩ := G₂
  simp only at hs ht
  subst hs
  subst ht
  have hp' : p₁ = p₂ := funext fun ℓ => Subtype.ext (hp ℓ ℓ rfl)
  have hm' : m₁ = m₂ := funext fun ℓ => hm ℓ ℓ rfl
  subst hp'
  subst hm'
  rfl

/-- **A couple code determines its carrier.** -/
theorem decodes_unique {Q : RegCpl} {G₁ G₂ : Garden 2} (h₁ : Q.Decodes G₁) (h₂ : Q.Decodes G₂) : G₁ = G₂ := by
  have ht : G₁.tree = G₂.tree := by
    funext j
    fin_cases j
    · exact h₁.2.1.trans h₂.2.1.symm
    · exact h₁.2.2.1.trans h₂.2.2.1.symm
  refine garden_ext (h₁.1.2.trans h₂.1.2.symm) ht (fun ℓ₁ ℓ₂ he => ?_) (fun ℓ₁ ℓ₂ _ => by
    rw [h₁.1.1 ℓ₁, h₂.1.1 ℓ₂])
  have hy := h₁.2.2.2 ℓ₁
  have hz := h₂.2.2.2 ℓ₂
  rw [← he] at hz
  exact decodedPair_functional Q hy hz

/-- **A chain code and a root sign determine the tree carrier.** -/
theorem decodesTree_unique {X : RegChain} {G₁ G₂ : Garden 1} (h₁ : X.DecodesTree G₁) (h₂ : X.DecodesTree G₂)
    (hs : G₁.sig 0 = G₂.sig 0) : G₁ = G₂ := by
  have hsig : G₁.sig = G₂.sig := by
    funext j
    fin_cases j
    exact hs
  have ht : G₁.tree = G₂.tree := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [h₁.1, h₂.1, hs]
  refine garden_ext hsig ht (fun ℓ₁ ℓ₂ he => ?_) (fun ℓ₁ ℓ₂ he => by rw [h₁.2.1 ℓ₁, h₂.2.1 ℓ₂, he])
  by_cases hl : ℓ₁.1.2 = X.lonePath
  · have hm₁ : G₁.mark ℓ₁ ≠ none := by rw [h₁.2.1 ℓ₁, ite_eq_left hl]; simp
    have hm₂ : G₂.mark ℓ₂ ≠ none := by
      rw [h₂.2.1 ℓ₂, ite_eq_left (by rw [← he]; exact hl)]; simp
    rw [(G₁.pair_eq_iff ℓ₁).2 hm₁, (G₂.pair_eq_iff ℓ₂).2 hm₂, he]
  · have hy := h₁.2.2 ℓ₁ hl
    have hz := h₂.2.2 ℓ₂ (by rw [← he]; exact hl)
    rw [← he, ← hs] at hz
    exact functional_of_flat_nodup (chain_pairs_flat_nodup X (G₁.sig 0) ((0 : Fin 1), [])).1 hy hz

theorem layeredGarden_ext {w : ℕ} {L₁ L₂ : LayeredGarden w} (hg : L₁.garden = L₂.garden)
    (hl : ∀ z : Fin w × Path, layerAt L₁ z = layerAt L₂ z) : L₁ = L₂ := by
  obtain ⟨g₁, l₁, i₁⟩ := L₁
  obtain ⟨g₂, l₂, i₂⟩ := L₂
  simp only at hg
  subst hg
  have : l₁ = l₂ := funext fun a => by
    have h := hl a.1
    rwa [layerAt_node ⟨g₁, l₁, i₁⟩ a, layerAt_node ⟨g₁, l₂, i₂⟩ a] at h
  subst this
  rfl

/-- **The coherent carrier of a couple with `q = q'` is unique.** -/
theorem coherentCouple_unique {p q : ℕ} {Q : RegCpl} {L₁ L₂ : LayeredGarden 2}
    (h₁ : IsCoherentCoupleAt p q q Q L₁) (h₂ : IsCoherentCoupleAt p q q Q L₂) : L₁ = L₂ := by
  have hg := decodes_unique h₁.2.1 h₂.2.1
  refine layeredGarden_ext hg fun z => ?_
  have l₁ := coherentCouple_layer_eq h₁
  have l₂ := coherentCouple_layer_eq h₂
  unfold layerAt
  by_cases hz : z.2 ∈ (L₁.garden.tree z.1).nodes
  · have hz' : z.2 ∈ (L₂.garden.tree z.1).nodes := by rw [← hg]; exact hz
    rw [dite_eq_left_of_eq_true (eq_true hz), dite_eq_left_of_eq_true (eq_true hz')]
    exact (l₁ ⟨z, hz⟩).trans (l₂ ⟨z, hz'⟩).symm
  · have hz' : ¬ z.2 ∈ (L₂.garden.tree z.1).nodes := by rw [← hg]; exact hz
    rw [dite_eq_right_of_eq_false (eq_false hz), dite_eq_right_of_eq_false (eq_false hz')]

/-- **The coherent carrier of a tree with `q = q'` and a given root sign is unique.** -/
theorem coherentTree_unique {p q : ℕ} {X : RegChain} {L₁ L₂ : LayeredGarden 1}
    (h₁ : IsCoherentTreeAt p q q X L₁) (h₂ : IsCoherentTreeAt p q q X L₂)
    (hs : L₁.garden.sig 0 = L₂.garden.sig 0) : L₁ = L₂ := by
  have hg := decodesTree_unique h₁.2.1 h₂.2.1 hs
  refine layeredGarden_ext hg fun z => ?_
  have l₁ := coherentTree_layer_eq h₁
  have l₂ := coherentTree_layer_eq h₂
  unfold layerAt
  by_cases hz : z.2 ∈ (L₁.garden.tree z.1).nodes
  · have hz' : z.2 ∈ (L₂.garden.tree z.1).nodes := by rw [← hg]; exact hz
    rw [dite_eq_left_of_eq_true (eq_true hz), dite_eq_left_of_eq_true (eq_true hz')]
    exact (l₁ ⟨z, hz⟩).trans (l₂ ⟨z, hz'⟩).symm
  · have hz' : ¬ z.2 ∈ (L₂.garden.tree z.1).nodes := by rw [← hg]; exact hz
    rw [dite_eq_right_of_eq_false (eq_false hz), dite_eq_right_of_eq_false (eq_false hz')]

end WaveTurbulence.PL234
