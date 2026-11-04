/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.SourceCodeOperations

/-! # Exact grafting of any couple code at an actual oriented leaf pair -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Replace one actual leaf-pair slot by a whole couple, then normalize its structure data. -/
def graftCouple (Q : RegCpl) (x y : Fin 2 × Path) (C : RegCpl) : RegCpl :=
  normalizeCouple (substituteCouplePair Q (0,[]) (1,[]) x y C)

/-- The actual oriented graft pair list, including every inserted source pair. -/
theorem graftCouple_pairs_perm (Q : RegCpl) (x y : Fin 2 × Path) (C : RegCpl)
    (hxy : (x,y) ∈ Q.raw.2) :
    (graftCouple Q x y C).raw.2.Perm (Q.raw.2.erase (x,y) ++ C.pairsAt x y) := by
  apply (normalizeCouple_pairs_perm _).trans
  change ((substituteCouplePair Q (0,[]) (1,[]) x y C).pairsAt (0,[]) (1,[])).Perm _
  rw [substituteCouplePair_pairsAt]
  exact splicePairs_perm_erase_append Q.raw.2 (x,y) (C.pairsAt x y) (decodedPair_nodup Q) hxy

/-- Distinct actual leaves root incomparable subtrees. -/
theorem leaf_addresses_incomp {w : ℕ} (tree : Fin w → TTree) (x y : Fin w × Path)
    (hx : x.2 ∈ (tree x.1).leaves) (hy : y.2 ∈ (tree y.1).leaves) (hne : x ≠ y) : IncompAddr x y := by
  have hnot : ∀ (u v : Fin w × Path), u.2 ∈ (tree u.1).leaves → v.2 ∈ (tree v.1).leaves →
      u ≠ v → ¬ Below u v := by
    intro u v hu hv hne h
    have hvn : v.2 ∈ (tree u.1).nodes := by
      rw [← h.1]
      exact TTree.leaves_subset_nodes _ hv
    have he := leaf_prefix_node_eq hu hvn h.2
    exact hne (Prod.ext h.1.symm he)
  exact ⟨hnot x y hx hy hne,hnot y x hy hx hne.symm⟩

/-- The roots of every actual oriented pair are incomparable. -/
theorem decodedPair_roots_incomp (Q : RegCpl) (x y : Fin 2 × Path) (hxy : (x,y) ∈ Q.raw.2) :
    IncompAddr x y := by
  have hv := decodedCouple_pairs_valid Q (x,y) hxy
  apply leaf_addresses_incomp (coupleForest Q) x y hv.1 hv.2
  intro he
  have hf := decodedPair_no_fixed Q x
  rw [he] at hxy
  exact decodedPair_no_fixed Q y ((mem_symmPairs_iff _ _).mpr (Or.inl hxy))

/-- Whole-couple grafting has precisely the literal source pair-graft tree shapes. -/
theorem graftCouple_forest (Q : RegCpl) (x y : Fin 2 × Path) (C : RegCpl)
    (hxy : (x,y) ∈ Q.raw.2) :
    coupleForest (graftCouple Q x y C) =
      updateAddressForest (updateAddressForest (coupleForest Q) x C.trees.1) y C.trees.2 := by
  let ℓ : GLeaf (coupleForest Q) := ⟨x,(decodedCouple_pairs_valid Q (x,y) hxy).1⟩
  let q : GLeaf (coupleForest Q) := ⟨y,(decodedCouple_pairs_valid Q (x,y) hxy).2⟩
  have hyx : y ≠ x := by
    intro he
    rw [he] at hxy
    exact decodedPair_no_fixed Q x ((mem_symmPairs_iff _ _).mpr (Or.inl hxy))
  have hq : q ≠ ℓ := fun he => hyx (congrArg Subtype.val he)
  let M := decodedCouple C
  have hleaf : forestSet (coupleForest (graftCouple Q x y C)) TTree.leaves =
      forestSet (Comb.graftLeafPairForest (coupleForest Q) ℓ q hq (M.tree 0) (M.tree 1)) TTree.leaves := by
    rw [coupleForest_leaf_set,graftPair_leaf_set,coupleForest_leaf_set,
      pairEndpoints_perm (graftCouple_pairs_perm Q x y C hxy),pairEndpoints_append,pairEndpoints_erase Q x y hxy]
    change _ = (pairEndpoints Q.raw.2 \ {x,y}) ∪ leafAddresses C.trees.1 x ∪ leafAddresses C.trees.2 y
    rw [← couple_leafAddresses C x y]
    ac_rfl
  exact forest_eq_of_leaf_set_eq _ _ hleaf

end WaveTurbulence.Reg
