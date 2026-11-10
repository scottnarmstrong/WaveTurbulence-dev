/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.CodeOrders
public import WaveTurbulence.Foundations.RegStruct.CombSnapshot.Trees
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-! # Chain spines, lone slots, and bare-chain orders (DH21 Proposition 4.7)

The binary shape is the Catalan inner/rest shape of the source legal partition.
Couples decorating red/green pairs do not change this spine.
-/

@[expose] public section

namespace WaveTurbulence.Reg
open TTree

/-- Undecorated Catalan shape of the chain's pairs. -/
def chainShape : RegChain → BinaryTree Unit
  | .nil => .nil
  | .pair _ _ _ inner rest => .node () (chainShape inner) (chainShape rest)

/-- A bare regular chain has no nontrivial couple inserted into a red or green pair. -/
def BareChain : RegChain → Prop
  | .nil => True
  | .pair _ r g inner rest => r = .triv ∧ g = .triv ∧ BareChain inner ∧ BareChain rest

/-- A chain's lone position always has the root sign (including nested legal pairs). -/
theorem lonePath_sign (X : RegChain) (ζ : ℤˣ) : pathSign ζ X.lonePath = ζ := by
  cases X with
  | nil => simp [RegChain.lonePath, pathSign]
  | pair m r g i s =>
    rw [RegChain.lonePath]
    simp only [Comb.pathSign_append, lonePath_sign i, lonePath_sign s]
    obtain ⟨c,b⟩ := m
    fin_cases c <;> fin_cases b <;> simp [MiniTreeCode.lone, pathSign]
termination_by structural X

/-- Bare chains are automatically well formed. -/
theorem bareChain_wf (X : RegChain) (hX : BareChain X) : X.wf = true := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    simp only [RegChain.wf, RegCpl.wf, Bool.true_and, bareChain_wf i hi, bareChain_wf s hs]
termination_by structural X

end WaveTurbulence.Reg
