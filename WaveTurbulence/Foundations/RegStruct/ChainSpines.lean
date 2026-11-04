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

/-- Total subtree extraction composes along path concatenation. -/
theorem subtreeAt_append (t : TTree) (p q : Path) :
    t.subtreeAt (p ++ q) = (t.subtreeAt p).subtreeAt q := by
  induction p generalizing t with
  | nil => rfl
  | cons i p ih =>
    cases t with
    | leaf => cases q <;> rfl
    | node l m r =>
      fin_cases i <;> simp [TTree.subtreeAt, ih]

/-- Filling the lone slot leaves the inserted subtree exactly at `lonePath`. -/
theorem plug_subtreeAt_lonePath (X : RegChain) (ζ : ℤˣ) (h : TTree) :
    (X.plug ζ h).subtreeAt X.lonePath = h := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    obtain ⟨c,b⟩ := m
    fin_cases c <;> fin_cases b <;>
      simp [RegChain.plug, RegChain.lonePath, node3, MiniTreeCode.lone,
        subtreeAt_append, TTree.subtreeAt, plug_subtreeAt_lonePath i, plug_subtreeAt_lonePath s]
termination_by structural X

/-- Bare chains are automatically well formed. -/
theorem bareChain_wf (X : RegChain) (hX : BareChain X) : X.wf = true := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    simp only [RegChain.wf, RegCpl.wf, Bool.true_and, bareChain_wf i hi, bareChain_wf s hs]
termination_by structural X

/-- A bare chain has two branching nodes for each pair in its Catalan shape. -/
theorem bareChain_size (X : RegChain) (hX : BareChain X) :
    X.size = 2 * (chainShape X).numNodes := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    obtain ⟨rfl,rfl,hi,hs⟩ := hX
    simp only [RegChain.size, RegCpl.size, chainShape, BinaryTree.numNodes,
      bareChain_size i hi, bareChain_size s hs]
    omega
termination_by structural X

/-- DH21 Prop 4.7's order identity for a decoded bare chain. -/
theorem bareChain_order (X : RegChain) (hX : BareChain X) (ζ : ℤˣ) :
    (X.plug ζ .leaf).order = 2 * (chainShape X).numNodes := by
  rw [code_plug_order, bareChain_size X hX]
  rfl

end WaveTurbulence.Reg
