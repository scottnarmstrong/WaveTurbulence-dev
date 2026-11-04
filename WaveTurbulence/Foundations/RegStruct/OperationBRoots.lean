/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.RootAddressMaps
public import WaveTurbulence.Foundations.RegStruct.RawRepresentation

/-! # Full source fidelity of operation B at either original root (DH21 Proposition 4.8, case 3) -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Code operation B, followed by the proved terminal normalization. -/
def operationB (Q : RegCpl) (target : Fin 2 × Path) (m : MiniTreeCode) : RegCpl :=
  normalizeCouple (insertMiniCouple Q (0,[]) (1,[]) target m)

/-- A missing negative chain contributes no pairs or path shift. -/
theorem type2_left_pairsAt {w : ℕ} (X : RegChain) (Q : RegCpl) (a b : Fin w × Path) :
    (RegCpl.type2 X .nil Q).pairsAt a b =
      X.pairsAt 1 a ++ Q.pairsAt (addrExt a X.lonePath) b := by
  simp [RegCpl.pairsAt,RegChain.pairsAt,RegChain.lonePath,addrExt]

/-- A missing positive chain contributes no pairs or path shift. -/
theorem type2_right_pairsAt {w : ℕ} (X : RegChain) (Q : RegCpl) (a b : Fin w × Path) :
    (RegCpl.type2 .nil X Q).pairsAt a b =
      X.pairsAt (-1) b ++ Q.pairsAt a (addrExt b X.lonePath) := by
  simp [RegCpl.pairsAt,RegChain.pairsAt,RegChain.lonePath,addrExt]

/-- At the positive root the normalized code has exactly the source raw pair list. -/
theorem operationB_left_pairs_perm (Q : RegCpl) (m : MiniTreeCode) :
    (operationB Q (0,[]) m).raw.2.Perm (Q.raw.opB (0,[]) m).2 := by
  rw [operationB,insertMiniCouple_at_left]
  apply (normalizeCouple_pairs_perm _).trans
  rw [raw_opB_root_pairs,nodeSign_root_zero]
  change ((RegCpl.type2 (miniChain m) .nil Q).pairsAt (0,[]) (1,[])).Perm _
  rw [type2_left_pairsAt]
  let f := prefixTree (0 : Fin 2) [m.c,m.lone]
  have hmap : Q.pairsAt (addrExt (0,[]) (miniChain m).lonePath) (1,[]) =
      Q.raw.2.map (fun p => (f p.1,f p.2)) := by
    have h := couple_pairsAt_map Q f (prefixTree_respects _ _) (0,[]) (1,[])
    simpa [f,RegCpl.raw,miniChain_lonePath,addrExt,prefixTree] using h
  rw [hmap]
  exact List.perm_append_comm

/-- At the negative root the same statement holds with its original negative sign. -/
theorem operationB_right_pairs_perm (Q : RegCpl) (m : MiniTreeCode) :
    (operationB Q (1,[]) m).raw.2.Perm (Q.raw.opB (1,[]) m).2 := by
  rw [operationB,insertMiniCouple_at_right Q (0,[]) (1,[]) (by decide)]
  apply (normalizeCouple_pairs_perm _).trans
  rw [raw_opB_root_pairs,nodeSign_root_one]
  change ((RegCpl.type2 .nil (miniChain m) Q).pairsAt (0,[]) (1,[])).Perm _
  rw [type2_right_pairsAt]
  let f := prefixTree (1 : Fin 2) [m.c,m.lone]
  have hmap : Q.pairsAt (0,[]) (addrExt (1,[]) (miniChain m).lonePath) =
      Q.raw.2.map (fun p => (f p.1,f p.2)) := by
    have h := couple_pairsAt_map Q f (prefixTree_respects _ _) (0,[]) (1,[])
    simpa [f,RegCpl.raw,miniChain_lonePath,addrExt,prefixTree] using h
  rw [hmap]
  exact List.perm_append_comm

/-- The root case of B preserves all literal pairs. -/
theorem operationB_root_pairs_perm (Q : RegCpl) (j : Fin 2) (m : MiniTreeCode) :
    (operationB Q (j,[]) m).raw.2.Perm (Q.raw.opB (j,[]) m).2 := by
  fin_cases j
  · exact operationB_left_pairs_perm Q m
  · exact operationB_right_pairs_perm Q m

/-- At the positive root the two actual tree shapes agree with the source operation. -/
theorem operationB_left_forest (Q : RegCpl) (m : MiniTreeCode) :
    coupleForest (operationB Q (0,[]) m) = (Q.raw.opB (0,[]) m).tree := by
  rw [raw_opB_update,raw_tree_eq_coupleForest]
  funext j
  fin_cases j <;>
    simp [operationB,coupleForest,normalizeCouple_trees,insertMiniCouple_at_left,
      RegCpl.trees,RegChain.plug,miniChain_plug,updateAddressForest,
      Function.update,Comb.replaceAt,TTree.subtreeAt]

/-- At the negative root the exact tree shape is the same mini-tree context. -/
theorem operationB_right_forest (Q : RegCpl) (m : MiniTreeCode) :
    coupleForest (operationB Q (1,[]) m) = (Q.raw.opB (1,[]) m).tree := by
  rw [raw_opB_update,raw_tree_eq_coupleForest]
  funext j
  fin_cases j <;>
    simp [operationB,coupleForest,normalizeCouple_trees,insertMiniCouple_at_right,
      RegCpl.trees,RegChain.plug,miniChain_plug,updateAddressForest,
      Function.update,Comb.replaceAt,TTree.subtreeAt]

/-- The root case of B preserves both source tree shapes. -/
theorem operationB_root_forest (Q : RegCpl) (j : Fin 2) (m : MiniTreeCode) :
    coupleForest (operationB Q (j,[]) m) = (Q.raw.opB (j,[]) m).tree := by
  fin_cases j
  · exact operationB_left_forest Q m
  · exact operationB_right_forest Q m

/-- Every raw B-step adds two pairs to the source list. -/
theorem raw_opB_pairs_length (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode) :
    (R.opB a m).2.length = R.2.length + 2 := by
  change (R.2.map _ ++ [_,_]).length = _
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]

/-- A B-step at either root adds exactly two branching nodes to the decoded code. -/
theorem operationB_root_size (Q : RegCpl) (j : Fin 2) (m : MiniTreeCode) :
    (operationB Q (j,[]) m).size = Q.size + 2 := by
  have hl := (operationB_root_pairs_perm Q j m).length_eq
  rw [raw_opB_pairs_length] at hl
  change ((operationB Q (j,[]) m).pairsAt (0,[]) (1,[])).length =
    (Q.pairsAt (0,[]) (1,[])).length + 2 at hl
  rw [couple_pairsAt_length,couple_pairsAt_length] at hl
  omega

/-- B always returns well-formed data after normalization. -/
theorem operationB_wf (Q : RegCpl) (a : Fin 2 × Path) (m : MiniTreeCode) :
    (operationB Q a m).wf = true := normalizeCouple_wf _

end WaveTurbulence.Reg
