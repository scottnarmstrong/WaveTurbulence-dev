/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ExplicitCoherentZero
/-! Every actual zero-order couple has the unique trivial regular code. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset WaveTurbulence.Reg

theorem tree_leaf_of_garden_order_zero {w : ℕ} (G : Garden w) (ho : G.order = 0) :
    ∀ j, G.tree j = TTree.leaf := by
  intro j
  have hj : (G.tree j).order ≤ G.order :=
    single_le_sum (f := fun i => (G.tree i).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have hz : (G.tree j).order = 0 := by omega
  cases ht : G.tree j <;> simp_all only [TTree.order] <;> omega

theorem trivial_decodes_of_couple_zero (G : Garden 2) (hc : IsCouple G) (ho : G.order = 0) :
    RegCpl.triv.Decodes G := by
  have ht := tree_leaf_of_garden_order_zero G ho
  have hp0 : G.pair (leafRoot G.tree ht 0) = leafRoot G.tree ht 1 :=
    (leafForestLeafEquiv G.tree ht).injective (leafPair_pair_root_zero G ht hc.1)
  have hp1 : G.pair (leafRoot G.tree ht 1) = leafRoot G.tree ht 0 := by
    rw [← hp0, G.pair_pair]
  refine ⟨hc, ht 0, ht 1, ?_⟩
  intro l
  have hl : l = leafRoot G.tree ht l.1.1 :=
    (leafForestLeafEquiv G.tree ht).injective rfl
  rcases hidx : l.1.1 with ⟨j, hj⟩
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · have hl0 : l = leafRoot G.tree ht 0 := by
      rw [hidx] at hl
      exact hl.trans (congrArg (leafRoot G.tree ht) (Fin.ext rfl))
    rw [hl0, hp0]
    simp only [RegCpl.raw, RegCpl.pairsAt, symmPairs, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, leafRoot, List.map_cons, List.map_nil,
      Prod.swap_prod_mk, true_or]
  · have hl1 : l = leafRoot G.tree ht 1 := by
      rw [hidx] at hl
      exact hl.trans (congrArg (leafRoot G.tree ht) (Fin.ext rfl))
    rw [hl1, hp1]
    simp only [RegCpl.raw, RegCpl.pairsAt, symmPairs, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, leafRoot, List.map_cons, List.map_nil,
      Prod.swap_prod_mk, or_true]

end WaveTurbulence.LGSpine
