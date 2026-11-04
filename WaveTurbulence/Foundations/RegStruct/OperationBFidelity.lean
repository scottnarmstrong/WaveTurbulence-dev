/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ReplacementLeafMembership

/-! # Full source tree fidelity of operation B at arbitrary nodes -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- A global rooted-address occurrence is exactly a node in the two-tree forest. -/
theorem coupleForest_node_iff (Q : RegCpl) (z : Fin 2 × Path) :
    z.2 ∈ (coupleForest Q z.1).nodes ↔ z ∈ coupleNodes Q (0,[]) (1,[]) := by
  rw [← couple_nodeAddresses]
  obtain ⟨j,p⟩ := z
  fin_cases j <;> simp [coupleForest,nodeAddresses,addrExt]

/-- Global leaf-set cardinality depends only on the total branching order. -/
theorem forest_leaf_set_card {w : ℕ} (tree : Fin w → TTree) :
    (forestSet tree TTree.leaves).card = 2 * (∑ j, (tree j).order) + w := by
  rw [Comb.card_forestSet]
  simp only [Comb.card_leaves,Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

/-- All code-B leaves occur in the source-B forest. -/
theorem operationB_leaf_set_subset (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ coupleNodes Q (0,[]) (1,[])) :
    forestSet (coupleForest (operationB Q target m)) TTree.leaves ⊆
      forestSet (Q.raw.opB target m).tree TTree.leaves := by
  have ha : target.2 ∈ (Q.raw.tree target.1).nodes := by
    rw [raw_tree_eq_coupleForest]
    exact (coupleForest_node_iff Q target).mpr ht
  rw [coupleForest_leaf_set,pairEndpoints_perm (operationB_pairs_perm Q target m ht),
    raw_opB_pairs,pairEndpoints_append]
  apply Finset.union_subset _ (raw_opB_new_endpoints Q.raw target m ha)
  intro z hz
  obtain ⟨p,hp,hz⟩ := (mem_pairEndpoints_iff _ _).mp hz
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hv := decodedCouple_pairs_valid Q q hq
  rcases hz with h | h
  · subst z
    apply (mem_forestSet _).mpr
    exact raw_opB_old_leaf Q.raw target q.1 m ha (by simpa only [raw_tree_eq_coupleForest] using hv.1)
  · subst z
    apply (mem_forestSet _).mpr
    exact raw_opB_old_leaf Q.raw target q.2 m ha (by simpa only [raw_tree_eq_coupleForest] using hv.2)

/-- At every actual node, normalized code B has precisely the source trees. -/
theorem operationB_forest (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode)
    (ht : target ∈ coupleNodes Q (0,[]) (1,[])) :
    coupleForest (operationB Q target m) = (Q.raw.opB target m).tree := by
  apply forest_eq_of_leaf_set_eq
  apply Finset.eq_of_subset_of_card_le (operationB_leaf_set_subset Q target m ht)
  have ha : target.2 ∈ (Q.raw.tree target.1).nodes := by
    rw [raw_tree_eq_coupleForest]
    exact (coupleForest_node_iff Q target).mpr ht
  have hord := raw_opB_order Q.raw target m ha
  have hQ : (∑ j, (Q.raw.tree j).order) = Q.size := by
    rw [raw_tree_eq_coupleForest]
    simpa only [coupleForest,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using code_trees_order Q
  have hnew : (∑ j, (coupleForest (operationB Q target m) j).order) = (operationB Q target m).size := by
    simpa only [coupleForest,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using
      code_trees_order (operationB Q target m)
  rw [forest_leaf_set_card,forest_leaf_set_card,hnew,hord,hQ,operationB_size Q target m ht]

end WaveTurbulence.Reg
