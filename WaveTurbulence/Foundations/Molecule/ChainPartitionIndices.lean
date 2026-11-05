/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainPartitions

/-! # Literal first/inner/rest partner formulas on the ordered chain spine -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Equality relabeling transports each actual partner, not just its cardinality. -/
theorem PairPartition.cast_pair {n m : ℕ} (h : n = m) (P : PairPartition n) (i : Fin n) :
    (P.cast h).pair (Fin.cast h i) = Fin.cast h (P.pair i) := by cases h; rfl

/-- The inner/rest decomposition has the source's two additional outer endpoints. -/
theorem chain_pair_spine_length (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) :
    (i.lonePath.length+2)+s.lonePath.length = (RegChain.pair k r g i s).lonePath.length := by
  simp only [RegChain.lonePath,List.length_append,List.length_singleton]
  omega

/-- The first top-to-bottom branching-node index. -/
def chainFirstIndex (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) :
    Fin (RegChain.pair k r g i s).lonePath.length :=
  Fin.cast (chain_pair_spine_length k r g i s) (Fin.castAdd s.lonePath.length 0)

/-- Embed an inner-chain index between the new pair endpoints. -/
def chainInnerIndex (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (j : Fin i.lonePath.length) :
    Fin (RegChain.pair k r g i s).lonePath.length :=
  Fin.cast (chain_pair_spine_length k r g i s) (Fin.castAdd s.lonePath.length j.castSucc.succ)

/-- Embed a rest-chain index strictly after the outer pair's second endpoint. -/
def chainRestIndex (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) (j : Fin s.lonePath.length) :
    Fin (RegChain.pair k r g i s).lonePath.length :=
  Fin.cast (chain_pair_spine_length k r g i s) (Fin.natAdd (i.lonePath.length+2) j)

/-- The first node pairs with the node after the complete inner chain. -/
theorem chainPartition_first_partner (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain) :
    ((chainPartition (.pair k r g i s)).pair (chainFirstIndex k r g i s)).val = i.lonePath.length+1 := by
  change (((((chainPartition i).enclose).append (chainPartition s)).cast
    (chain_pair_spine_length k r g i s)).pair
      (Fin.cast (chain_pair_spine_length k r g i s) (Fin.castAdd s.lonePath.length 0))).val = _
  rw [PairPartition.cast_pair,PairPartition.append_pair_left]
  change (PairPartition.enclosePartner (chainPartition i) 0).val = _
  rw [PairPartition.enclosePartner_zero]
  rfl

/-- Every inner partner retains its actual position shifted by one. -/
theorem chainPartition_inner_partner (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (j : Fin i.lonePath.length) :
    (chainPartition (.pair k r g i s)).pair (chainInnerIndex k r g i s j) =
      chainInnerIndex k r g i s ((chainPartition i).pair j) := by
  change (((((chainPartition i).enclose).append (chainPartition s)).cast
    (chain_pair_spine_length k r g i s)).pair
      (Fin.cast (chain_pair_spine_length k r g i s) (Fin.castAdd s.lonePath.length j.castSucc.succ))) = _
  rw [PairPartition.cast_pair,PairPartition.append_pair_left]
  change Fin.cast _ (Fin.castAdd _ (PairPartition.enclosePartner (chainPartition i) j.castSucc.succ)) = _
  rw [PairPartition.enclosePartner_inner]
  rfl

/-- Every rest partner retains its actual position shifted past both outer endpoints and the inner chain. -/
theorem chainPartition_rest_partner (k : MiniTreeCode) (r g : RegCpl) (i s : RegChain)
    (j : Fin s.lonePath.length) :
    (chainPartition (.pair k r g i s)).pair (chainRestIndex k r g i s j) =
      chainRestIndex k r g i s ((chainPartition s).pair j) := by
  change (((((chainPartition i).enclose).append (chainPartition s)).cast
    (chain_pair_spine_length k r g i s)).pair
      (Fin.cast (chain_pair_spine_length k r g i s) (Fin.natAdd (i.lonePath.length+2) j))) = _
  rw [PairPartition.cast_pair,PairPartition.append_pair_right]
  rfl

end WaveTurbulence.Reg
