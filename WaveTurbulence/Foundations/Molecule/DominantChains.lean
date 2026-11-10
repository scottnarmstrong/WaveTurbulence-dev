/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.ChainPartitions
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut

/-! # The source dominant partition and the pinned B2 dominant-chain definition -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Only an empty chain has an empty spine. -/
theorem chain_lonePath_length_zero_iff (X : RegChain) : X.lonePath.length = 0 ↔ X = .nil := by
  cases X with
  | nil => simp [RegChain.lonePath]
  | pair k r g i s =>
    simp only [RegChain.lonePath,List.length_append,List.length_singleton,reduceCtorEq,iff_false]
    omega

end WaveTurbulence.Reg
