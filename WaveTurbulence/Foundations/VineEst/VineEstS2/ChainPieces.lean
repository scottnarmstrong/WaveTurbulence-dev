/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.VineChainConnected

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CurrentBlocks
public import WaveTurbulence.Foundations.VineEst.VineEstS2.ChainInteriorPartition

/-! # Actual vine-chain ingredients partition its interior branches -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- One actual source vine with ordered joints. -/
structure ChainPiece (M : Molecule V D) where
  vineType : VineType
  atoms : Finset V
  upper : V
  lower : V
  vine : M.IsVine vineType atoms upper lower

end WaveTurbulence.VineEstS2
