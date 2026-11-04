/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.GeneralCoupleGraft

/-! # Exact extraction and valid source positions inside a whole-couple graft -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- A valid address update extracts precisely its inserted subtree. -/
theorem updateAddressForest_extract {w : ℕ} (tree : Fin w → TTree) (a : Fin w × Path) (u s : TTree)
    (ha : Comb.subtree (tree a.1) a.2 = some u) :
    Comb.subtree (updateAddressForest tree a s a.1) a.2 = some s := by
  rw [updateAddressForest,Function.update_self,Comb.subtree_replaceAt ha]

/-- An incomparable address update preserves the other actual subtree. -/
theorem updateAddressForest_extract_disjoint {w : ℕ} (tree : Fin w → TTree) (a b : Fin w × Path)
    (s : TTree) (hab : IncompAddr a b) :
    Comb.subtree (updateAddressForest tree a s b.1) b.2 = Comb.subtree (tree b.1) b.2 := by
  by_cases hj : b.1 = a.1
  · have hp : ¬ a.2 <+: b.2 := fun h => hab.1 ⟨hj,h⟩
    have hq : ¬ b.2 <+: a.2 := fun h => hab.2 ⟨hj.symm,h⟩
    rw [updateAddressForest,hj,Function.update_self,Comb.subtree_replaceAt_disjoint _ _ _ hp hq]
  · rw [updateAddressForest,Function.update_of_ne hj]

/-- The two leaf roots of the whole-couple graft extract its exact positive and negative trees. -/
theorem graftCouple_extract (Q C : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2) :
    Comb.subtree (coupleForest (graftCouple Q x y C) x.1) x.2 = some C.trees.1 ∧
      Comb.subtree (coupleForest (graftCouple Q x y C) y.1) y.2 = some C.trees.2 := by
  have hi := decodedPair_roots_incomp Q x y hxy
  have hv := decodedCouple_pairs_valid Q (x,y) hxy
  have hx := Comb.subtree_of_mem_leaves hv.1
  have hy := Comb.subtree_of_mem_leaves hv.2
  rw [graftCouple_forest Q x y C hxy]
  constructor
  · rw [updateAddressForest_extract_disjoint _ y x C.trees.2 hi.symm]
    exact updateAddressForest_extract (coupleForest Q) x .leaf C.trees.1 hx
  · apply updateAddressForest_extract _ y .leaf C.trees.2
    rw [updateAddressForest_extract_disjoint _ x y C.trees.1 hi]
    exact hy

/-- A node of the inserted code gives an actual node at its literal globally framed address. -/
theorem graftCouple_node_mem (Q C : RegCpl) (x y z : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (hz : z ∈ coupleNodes C (0,[]) (1,[])) :
    frameAddress x y z ∈ coupleNodes (graftCouple Q x y C) (0,[]) (1,[]) := by
  have hroots := graftCouple_extract Q C x y hxy
  have he := frameAddress_subtree (coupleForest (graftCouple Q x y C)) x y C hroots.1 hroots.2 z
  obtain ⟨u,hu⟩ := (Comb.subtree_exists_iff _ _).mpr ((coupleForest_node_iff C z).mpr hz)
  apply (coupleForest_node_iff _ _).mp
  apply (Comb.subtree_exists_iff _ _).mp
  exact ⟨u,he.trans hu⟩

/-- Every literal inserted source pair remains a literal pair of the grafted code. -/
theorem graftCouple_pair_mem (Q C : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ C.raw.2) :
    (frameAddress x y p.1,frameAddress x y p.2) ∈ (graftCouple Q x y C).raw.2 := by
  apply (graftCouple_pairs_perm Q x y C hxy).mem_iff.mpr
  apply List.mem_append_right
  rw [pairsAt_frameAddress]
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

/-- Whole-couple grafting depends on the actual inserted carrier, not its construction history. -/
theorem graftCouple_carrier_congr (Q C D : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2)
    (he : decodedCouple C = decodedCouple D) :
    decodedCouple (graftCouple Q x y C) = decodedCouple (graftCouple Q x y D) := by
  have hp : (C.pairsAt x y).Perm (D.pairsAt x y) := by
    rw [pairsAt_frameAddress,pairsAt_frameAddress]
    exact (rawPairs_perm_of_carrier_eq he).map _
  apply decodedCouple_eq_of_rawPairs_perm
  exact (graftCouple_pairs_perm Q x y C hxy).trans
    ((hp.append_left _).trans (graftCouple_pairs_perm Q x y D hxy).symm)

/-- Two exact representations of the same raw data give the same actual carrier. -/
theorem RawRep.carrier_eq {C D : RegCpl} {R : RawCpl} (hC : RawRep C R) (hD : RawRep D R) :
    decodedCouple C = decodedCouple D := decodedCouple_eq_of_rawPairs_perm C D (hC.2.symm.trans hD.2)

end WaveTurbulence.Reg
