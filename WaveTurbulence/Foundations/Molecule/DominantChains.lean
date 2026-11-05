/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.DominantPartitions
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # The source dominant partition and the pinned B2 dominant-chain definition -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- No nested inner pairs: exactly the source consecutive-pair chain grammar. -/
def ConsecutiveChain : RegChain → Prop
  | .nil => True
  | .pair _ _ _ i s => i = .nil ∧ ConsecutiveChain s

/-- Every couple decorating any chain pair is dominant. -/
def ChainSideDominant : RegChain → Prop
  | .nil => True
  | .pair _ r g i s => r.dominant = true ∧ g.dominant = true ∧ ChainSideDominant i ∧ ChainSideDominant s

/-- Equality relabeling retains the actual adjacency relation on indices. -/
theorem PairPartition.cast_adjacent_iff {n m : ℕ} (h : n = m) (P : PairPartition n) :
    (P.cast h).Adjacent ↔ P.Adjacent := by cases h; rfl

/-- Only an empty chain has an empty spine. -/
theorem chain_lonePath_length_zero_iff (X : RegChain) : X.lonePath.length = 0 ↔ X = .nil := by
  cases X with
  | nil => simp [RegChain.lonePath]
  | pair k r g i s =>
    simp only [RegChain.lonePath,List.length_append,List.length_singleton,reduceCtorEq,iff_false]
    omega

/-- The actual partner involution has adjacent pairs precisely when every inner parse is empty. -/
theorem chainPartition_adjacent_iff (X : RegChain) : (chainPartition X).Adjacent ↔ ConsecutiveChain X := by
  cases X with
  | nil => constructor; intro; trivial; intro _ i; exact Fin.elim0 i
  | pair k r g i s =>
    change (((((chainPartition i).enclose).append (chainPartition s)).cast _).Adjacent) ↔ _
    rw [PairPartition.cast_adjacent_iff,PairPartition.append_adjacent_iff,PairPartition.enclose_adjacent_iff,
      chain_lonePath_length_zero_iff,chainPartition_adjacent_iff s]
    rfl
termination_by structural X

/-- This is exactly the source partition `{0,1},{2,3},...`, without a relabeling quotient. -/
theorem chainPartition_dominant_iff (X : RegChain) : (chainPartition X).Dominant ↔ ConsecutiveChain X :=
  (PairPartition.dominant_iff_adjacent _).trans (chainPartition_adjacent_iff X)

/-- The pinned B2 boolean means consecutive source pairs and dominant actual side data. -/
theorem chain_dominant_iff_consecutive_and_sides (X : RegChain) :
    X.dominant = true ↔ ConsecutiveChain X ∧ ChainSideDominant X := by
  cases X with
  | nil => simp [RegChain.dominant,ConsecutiveChain,ChainSideDominant]
  | pair k r g i s =>
    cases i with
    | nil =>
      simp only [RegChain.dominant,RegChain.isNil,Bool.true_and,Bool.and_eq_true,
        ConsecutiveChain,ChainSideDominant,true_and,chain_dominant_iff_consecutive_and_sides s]
      tauto
    | pair l r' g' j t => simp [RegChain.dominant,RegChain.isNil,ConsecutiveChain]
termination_by structural X

/-- TARGET's dominant-chain condition agrees with the exact pinned B2 decoder data. -/
theorem chain_dominant_iff_partition_and_sides (X : RegChain) :
    X.dominant = true ↔ (chainPartition X).Dominant ∧ ChainSideDominant X := by
  rw [chain_dominant_iff_consecutive_and_sides,chainPartition_dominant_iff]

end WaveTurbulence.Reg
