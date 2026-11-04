/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAuxiliaryB

/-! # Literal pair lists and actual source positions of double-chain templates -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Omitting the redundant empty outer constructor preserves the complete literal pair list. -/
theorem joinChains_pair_list {w : ℕ} (p n : RegChain) (q : RegCpl) (a b : Fin w × Path) :
    (joinChains p n q).pairsAt a b = p.pairsAt 1 a ++ n.pairsAt (-1) b ++
      q.pairsAt (addrExt a p.lonePath) (addrExt b n.lonePath) := by
  cases p <;> cases n
  all_goals first
    | rfl
    | simp [joinChains,RegChain.isNil,RegChain.pairsAt,RegChain.lonePath,addrExt]

/-- The exact raw double-chain list, including its one terminal cross pair. -/
theorem doubleChain_pairs (p n : RegChain) :
    (joinChains p n .triv).raw.2 = p.pairsAt 1 (0,[]) ++ n.pairsAt (-1) (1,[]) ++
      [(((0 : Fin 2),p.lonePath),(1,n.lonePath))] := by
  change (joinChains p n .triv).pairsAt (0,[]) (1,[]) = _
  rw [joinChains_pair_list]
  simp only [RegCpl.pairsAt,addrExt,List.nil_append]

/-- Every positive-chain node or its lone position is an actual node of the double chain. -/
theorem doubleChain_positive_position (p n : RegChain) (target : Fin 2 × Path)
    (ht : target ∈ chainNodes p 1 (0,[]) ∨ target = addrExt (0,[]) p.lonePath) :
    target ∈ coupleNodes (joinChains p n .triv) (0,[]) (1,[]) := by
  have hm : target ∈ nodeAddresses (p.plug 1 .leaf) (0,[]) := by
    rw [chain_nodeAddresses,nodeAddresses_leaf]
    rcases ht with ht | ht
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr ht)
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  apply (coupleForest_node_iff _ _).mp
  change q ∈ (joinChains p n .triv).trees.1.nodes
  rw [joinChains_trees]
  exact hq

/-- Every negative-chain node or its lone position is likewise an actual double-chain node. -/
theorem doubleChain_negative_position (p n : RegChain) (target : Fin 2 × Path)
    (ht : target ∈ chainNodes n (-1) (1,[]) ∨ target = addrExt (1,[]) n.lonePath) :
    target ∈ coupleNodes (joinChains p n .triv) (0,[]) (1,[]) := by
  have hm : target ∈ nodeAddresses (n.plug (-1) .leaf) (1,[]) := by
    rw [chain_nodeAddresses,nodeAddresses_leaf]
    rcases ht with ht | ht
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr ht)
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hm
  apply (coupleForest_node_iff _ _).mp
  change q ∈ (joinChains p n .triv).trees.2.nodes
  rw [joinChains_trees]
  exact hq

end WaveTurbulence.Reg
