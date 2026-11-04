/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.OperationALists
public import WaveTurbulence.Foundations.RegStruct.PairErasure
public import WaveTurbulence.Foundations.RegStruct.GraftLeafSets
public import WaveTurbulence.Foundations.RegStruct.RawAddressUpdate
public import WaveTurbulence.Foundations.RegStruct.TreeRecovery

/-! # Full source fidelity of code operation A (DH21 Proposition 4.8, case 1)

Trees are recovered from the exact global leaf sets. Pair erasure removes
exactly the two old leaves, and COMB's graft bijection inserts exactly the
mini-couple leaves. The same proof handles both roots in one original tree.
-/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- A permutation preserves the actual endpoint set. -/
theorem pairEndpoints_perm {α : Type*} [DecidableEq α] {P Q : List (α × α)} (h : P.Perm Q) :
    pairEndpoints P = pairEndpoints Q := by
  ext z
  rw [mem_pairEndpoints_iff,mem_pairEndpoints_iff]
  constructor
  · rintro ⟨p,hp,hz⟩
    exact ⟨p,h.mem_iff.mp hp,hz⟩
  · rintro ⟨p,hp,hz⟩
    exact ⟨p,h.mem_iff.mpr hp,hz⟩

/-- Every decoded global leaf is precisely an endpoint of the raw pair list. -/
theorem coupleForest_leaf_set (Q : RegCpl) :
    forestSet (coupleForest Q) TTree.leaves = pairEndpoints Q.raw.2 := by
  ext z
  rw [mem_forestSet,← coupleForest_leaf_iff,couple_leafAddresses]
  rfl

/-- The three new source pairs are exactly the decoded mini-couple pairs. -/
theorem raw_opA_pair_list (R : RawCpl) (x y : Fin 2 × Path) (c : MiniCplCode) :
    (R.opA x y c).2 = R.2.erase (x,y) ++ (miniCoupleCode c).pairsAt x y := rfl

/-- Operation A on code data has exactly the two trees of the source operation. -/
theorem operationA_forest (Q : RegCpl) (x y : Fin 2 × Path) (c : MiniCplCode)
    (h : (x,y) ∈ Q.raw.2) :
    coupleForest (operationA Q x y c) = (Q.raw.opA x y c).tree := by
  let ℓ : GLeaf (coupleForest Q) := ⟨x,(decodedCouple_pairs_valid Q (x,y) h).1⟩
  let q : GLeaf (coupleForest Q) := ⟨y,(decodedCouple_pairs_valid Q (x,y) h).2⟩
  have hyx : y ≠ x := by
    intro he
    apply decodedPair_no_fixed Q x
    exact (mem_symmPairs_iff _ _).mpr (Or.inl (by simpa only [he] using h))
  have hq : q ≠ ℓ := fun he => hyx (congrArg Subtype.val he)
  let M := decodedCouple (miniCoupleCode c)
  have hm0 : M.tree 0 = .node .leaf .leaf .leaf := by
    change (miniCoupleCode c).trees.1 = _
    rfl
  have hm1 : M.tree 1 = .node .leaf .leaf .leaf := by
    change (miniCoupleCode c).trees.2 = _
    simp [miniCoupleCode,RegCpl.trees]
  have hraw : (Q.raw.opA x y c).tree =
      Comb.graftLeafPairForest (coupleForest Q) ℓ q hq (M.tree 0) (M.tree 1) := by
    rw [raw_opA_updates,raw_tree_eq_coupleForest,hm0,hm1]
    rfl
  have hleaves : forestSet (coupleForest (operationA Q x y c)) TTree.leaves =
      forestSet (Comb.graftLeafPairForest (coupleForest Q) ℓ q hq (M.tree 0) (M.tree 1)) TTree.leaves := by
    rw [coupleForest_leaf_set,graftPair_leaf_set,coupleForest_leaf_set,
      pairEndpoints_perm (operationA_pairs_perm Q x y c h),raw_opA_pair_list,
      pairEndpoints_append,pairEndpoints_erase Q x y h,
      ← couple_leafAddresses (miniCoupleCode c) x y]
    ac_rfl
  exact (forest_eq_of_leaf_set_eq _ _ hleaves).trans hraw.symm

end WaveTurbulence.Reg
