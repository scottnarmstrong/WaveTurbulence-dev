/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoupleZeroClassification
/-! Proper irreducible gardens have positive branching order; this closes the higher-garden base order. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem not_irreducible_of_plain_order_zero {w : ℕ} (hw : 4 ≤ w) (G : Garden w)
    (hplain : G.IsPlain) (ho : G.order = 0) : ¬ G.Irreducible := by
  classical
  have ht := tree_leaf_of_garden_order_zero G ho
  let l : GLeaf G.tree := leafRoot G.tree ht ⟨0, by omega⟩
  let A : Finset (Fin w) := {l.1.1, (G.pair l).1.1}
  have hnon : A.Nonempty := ⟨l.1.1, mem_insert_self _ _⟩
  have hcard : A.card ≤ 2 := card_le_two
  have hproper : A ≠ univ := by
    intro he
    have hc : A.card = w := by rw [he, card_univ, Fintype.card_fin]
    omega
  intro hi
  apply hi A hnon hproper
  intro x hx
  have hxA : x.1.1 ∈ A := (mem_filter.mp hx).2
  have hx' : x = l ∨ x = G.pair l := by
    rcases mem_insert.mp hxA with he | he
    · exact Or.inl ((leafForestLeafEquiv G.tree ht).injective he)
    · exact Or.inr ((leafForestLeafEquiv G.tree ht).injective (mem_singleton.mp he))
  refine ⟨fun he => ((G.pair_eq_iff x).mp he) (hplain x), ?_⟩
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rcases hx' with rfl | rfl
  · exact mem_insert_of_mem (mem_singleton_self _)
  · rw [G.pair_pair]
    exact mem_insert_self _ _

end WaveTurbulence.LGSpine
