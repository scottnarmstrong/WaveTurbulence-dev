/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PartitionAppendLegality
public import WaveTurbulence.Foundations.Molecule.PartitionEncloseLegality
public import WaveTurbulence.Foundations.RegStruct.SaturatedChainShape

/-! # Actual noncrossing partner involutions on a chain's ordered spine indices -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Relabel a finite pair partition along equality of its actual number of labels. -/
def PairPartition.cast {n m : ℕ} (h : n = m) (P : PairPartition n) : PairPartition m := h ▸ P

/-- Equality relabeling preserves source legality. -/
theorem PairPartition.cast_legal {n m : ℕ} (h : n = m) (P : PairPartition n) (hP : P.Legal) :
    (P.cast h).Legal := by cases h; exact hP

/-- The empty ordered partition. -/
def emptyPartition : PairPartition 0 where
  pair := Fin.elim0
  involutive := by intro i; exact Fin.elim0 i
  no_fixed := by intro i; exact Fin.elim0 i

/-- The chain-pair grammar gives the actual partner involution on its top-to-bottom spine labels. -/
def chainPartition : (X : RegChain) → PairPartition X.lonePath.length
  | .nil => emptyPartition
  | .pair _ _ _ i s =>
    (((chainPartition i).enclose).append (chainPartition s)).cast
      (by simp only [RegChain.lonePath,List.length_append,List.length_singleton]; omega)

/-- Every chain code has a legal, literally indexed source pair partition. -/
theorem chainPartition_legal (X : RegChain) : (chainPartition X).Legal := by
  cases X with
  | nil => intro a; exact Fin.elim0 a
  | pair k r g i s =>
    exact PairPartition.cast_legal _ _
      (PairPartition.append_legal _ _ (PairPartition.enclose_legal _ (chainPartition_legal i)) (chainPartition_legal s))
termination_by structural X

/-- There are exactly two spine nodes for each source pair, independent of side decorations. -/
theorem chain_lonePath_length (X : RegChain) : X.lonePath.length = 2 * (chainShape X).numNodes := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    simp only [RegChain.lonePath,List.length_append,List.length_singleton,chainShape,BinaryTree.numNodes,
      chain_lonePath_length i,chain_lonePath_length s]
    omega
termination_by structural X

/-- Every code's ordered spine has even length, and its actual partition has no fixed point. -/
theorem chain_spine_even (X : RegChain) : Even X.lonePath.length := by
  rw [chain_lonePath_length]
  exact ⟨(chainShape X).numNodes,by omega⟩

end WaveTurbulence.Reg
