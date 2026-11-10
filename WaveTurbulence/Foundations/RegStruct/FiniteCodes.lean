/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # Finiteness of bounded regular-object structure data (DH21 Corollary 4.9)

The finite-carrier construction is adapted from the audited B2 probe, independently
of all unfinished characterizations.
-/

public section

namespace WaveTurbulence.Reg

theorem chain_size_pos_of_not_isNil {X : RegChain} (h : X.isNil = false) : 2 ≤ X.size := by
  cases X with
  | nil => simp [RegChain.isNil] at h
  | pair => simp only [RegChain.size]; omega


end WaveTurbulence.Reg
