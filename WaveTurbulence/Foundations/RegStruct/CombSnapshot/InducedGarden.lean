/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.ForestEmbedding

/-! # Pairing-closed rooted subforests as actual gardens (TARGET L636, L846) -/

public section

namespace WaveTurbulence.Comb
open Finset

variable {w v : ℕ} {G : Garden w}

/-- The ambient leaf set selected by a rooted subforest. -/
@[expose] def RootedSubforest.leafSet (E : RootedSubforest G.tree v) : Finset (GLeaf G.tree) :=
  Finset.univ.image (RootedSubforest.leafEmbedding E)

/-- A leaf is in the selected set exactly when it is below a selected root. -/
theorem RootedSubforest.mem_leafSet_iff (E : RootedSubforest G.tree v) (ℓ : GLeaf G.tree) :
    ℓ ∈ RootedSubforest.leafSet E ↔ ∃ i, (E.root i).IsDesc ℓ.toNode := by
  constructor
  · intro h
    obtain ⟨ℓ', _, he⟩ := Finset.mem_image.mp h
    refine ⟨ℓ'.1.1, ?_⟩
    rw [← he]
    exact ⟨rfl, List.prefix_append _ _⟩
  · rintro ⟨i, hj, q, hq⟩
    have hl : q ∈ (E.shape i).leaves := by
      apply (subtree_leaves_iff (E.subtree_eq i) q).mpr
      rw [hq, hj]
      exact ℓ.2
    refine Finset.mem_image.mpr ⟨⟨(i, q), hl⟩, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact Prod.ext hj hq

/-- Complete pairing provides the partner-preimage data without an extra hypothesis. -/
theorem RootedSubforest.closed_partner (E : RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (RootedSubforest.leafSet E)) :
    ∀ ℓ, ∃ ℓ', RootedSubforest.leafEmbedding E ℓ' = G.pair (RootedSubforest.leafEmbedding E ℓ) := by
  intro ℓ
  have hm : RootedSubforest.leafEmbedding E ℓ ∈ RootedSubforest.leafSet E :=
    Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, rfl⟩
  obtain ⟨ℓ', _, he⟩ := Finset.mem_image.mp (hc _ hm).2
  exact ⟨ℓ', he⟩

/-- The induced garden of a completely paired rooted subforest. -/
@[expose] noncomputable def RootedSubforest.inducedGarden (E : RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (RootedSubforest.leafSet E)) : Garden v :=
  RootedSubforest.garden E (RootedSubforest.closed_partner E hc)

/-- The induced garden is plain even if the ambient garden has marks elsewhere. -/
theorem RootedSubforest.inducedGarden_plain (E : RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (RootedSubforest.leafSet E)) :
    (RootedSubforest.inducedGarden E hc).IsPlain := by
  intro ℓ
  change G.mark (RootedSubforest.leafEmbedding E ℓ) = none
  by_contra hm
  have he := (G.pair_eq_iff (RootedSubforest.leafEmbedding E ℓ)).mpr hm
  exact (hc _ (Finset.mem_image.mpr ⟨ℓ, Finset.mem_univ _, rfl⟩)).1 he

/-- The induced pairing is the ambient pairing under the leaf embedding. -/
theorem RootedSubforest.inducedGarden_pair (E : RootedSubforest G.tree v)
    (hc : G.CompletelyPaired (RootedSubforest.leafSet E)) (ℓ : GLeaf E.shape) :
    RootedSubforest.leafEmbedding E ((RootedSubforest.inducedGarden E hc).pair ℓ) =
      G.pair (RootedSubforest.leafEmbedding E ℓ) :=
  leafPairPullback_spec _ _ _

end WaveTurbulence.Comb
