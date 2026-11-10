/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LegalPartitions
public import Mathlib.Data.Fin.Tuple.Basic
public import WaveTurbulence.Foundations.RegStruct.ChainSpines

/-! # Actual noncrossing partner involutions on a chain's ordered spine indices -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- There are exactly two spine nodes for each source pair, independent of side decorations. -/
theorem chain_lonePath_length (X : RegChain) : X.lonePath.length = 2 * (chainShape X).numNodes := by
  cases X with
  | nil => rfl
  | pair k r g i s =>
    simp only [RegChain.lonePath,List.length_append,List.length_singleton,chainShape,BinaryTree.numNodes,
      chain_lonePath_length i,chain_lonePath_length s]
    omega
termination_by structural X

end WaveTurbulence.Reg
