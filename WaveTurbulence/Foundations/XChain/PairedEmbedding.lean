/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftTopChildren
/-! Completely paired finite sets transfer through an injective pairing-compatible leaf map. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem completelyPaired_map_iff {v w : ℕ} (G : Garden v) (H : Garden w)
    (e : GLeaf G.tree ↪ GLeaf H.tree)
    (hpair : ∀ ℓ, H.pair (e ℓ) = e (G.pair ℓ)) (S : Finset (GLeaf G.tree)) :
    H.CompletelyPaired (S.map e) ↔ G.CompletelyPaired S := by
  classical
  constructor
  · intro h ℓ hℓ
    obtain ⟨hne, hmem⟩ := h (e ℓ) (Finset.mem_map.mpr ⟨ℓ, hℓ, rfl⟩)
    refine ⟨fun he => hne (by rw [hpair, he]), ?_⟩
    rw [hpair] at hmem
    obtain ⟨a, ha, he⟩ := Finset.mem_map.mp hmem
    exact e.injective he ▸ ha
  · intro h a ha
    obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨hne, hmem⟩ := h ℓ hℓ
    refine ⟨fun he => hne (e.injective ((hpair ℓ).symm.trans he)), ?_⟩
    rw [hpair]
    exact Finset.mem_map.mpr ⟨G.pair ℓ, hmem, rfl⟩

end WaveTurbulence.Induct
