/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSpines
public import Mathlib.Data.Fintype.BigOperators

/-! # Catalan count for undecorated chains (DH21 Proposition 4.7, Corollary 4.9)

A chain is encoded by its noncrossing binary shape and one of six mini-tree
codes per pair. Two chains require the Catalan convolution, rather than the
single-chain Catalan number.
-/

@[expose] public section
namespace WaveTurbulence.Reg

/-- Mini-tree labels in the source's increasing-first-endpoint (preorder) ordering. -/
def chainLabels : RegChain → List MiniTreeCode
  | .nil => []
  | .pair m _ _ i s => m :: (chainLabels i ++ chainLabels s)

theorem chainLabels_length (X : RegChain) :
    (chainLabels X).length = (chainShape X).numNodes := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [chainLabels, List.length_cons, List.length_append, chainShape, BinaryTree.numNodes,
      chainLabels_length i, chainLabels_length s]
termination_by structural X

/-- A bare chain is determined by its Catalan shape and ordered mini-tree labels. -/
theorem bareChain_ext (X Y : RegChain) (hX : BareChain X) (hY : BareChain Y)
    (hs : chainShape X = chainShape Y) (hl : chainLabels X = chainLabels Y) : X = Y := by
  cases X with
  | nil =>
    cases Y with
    | nil => rfl
    | pair m r g i s => simp only [chainShape, reduceCtorEq] at hs
  | pair m r g i s =>
    cases Y with
    | nil => simp only [chainShape, reduceCtorEq] at hs
    | pair p r' g' i' s' =>
      obtain ⟨rfl,rfl,hi,ht⟩ := hX
      obtain ⟨rfl,rfl,hi',ht'⟩ := hY
      have hshape := BinaryTree.node.inj hs
      have hlabels := List.cons.inj hl
      have hlen : (chainLabels i).length = (chainLabels i').length := by
        rw [chainLabels_length, chainLabels_length, hshape.2.1]
      obtain ⟨hil,hsl⟩ := List.append_inj hlabels.2 hlen
      have hii := bareChain_ext i i' hi hi' hshape.2.1 hil
      have hss := bareChain_ext s s' ht ht' hshape.2.2 hsl
      have hmp := hlabels.1
      subst p; subst i'; subst s'
      rfl
termination_by structural X

/-- Finite counting data for a bare chain with `m` paired branching-node pairs. -/
def bareChainData (m : ℕ) (X : {X : RegChain // BareChain X ∧ (chainShape X).numNodes = m}) :
    ↥(BinaryTree.treesOfNumNodesEq m) × List.Vector MiniTreeCode m :=
  (⟨chainShape X.1, BinaryTree.mem_treesOfNumNodesEq.mpr X.2.2⟩,
    ⟨chainLabels X.1, (chainLabels_length X.1).trans X.2.2⟩)

theorem bareChainData_injective (m : ℕ) : Function.Injective (bareChainData m) := by
  intro X Y h
  apply Subtype.ext
  exact bareChain_ext X.1 Y.1 X.2.1 Y.2.1
    (congrArg Subtype.val (congrArg Prod.fst h))
    (congrArg List.Vector.toList (congrArg Prod.snd h))

theorem card_miniTreeCode : Fintype.card MiniTreeCode = 6 := by decide

/-- At most `catalan m * 6^m` undecorated chain codes (DH21 Cor 4.9). -/
theorem bareChain_count_le (m : ℕ) :
    Nat.card {X : RegChain // BareChain X ∧ (chainShape X).numNodes = m} ≤ catalan m * 6 ^ m := by
  have h := Nat.card_le_card_of_injective (bareChainData m) (bareChainData_injective m)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_coe, card_vector,
    card_miniTreeCode, BinaryTree.treesOfNumNodesEq_card_eq_catalan] using h

/-- The correct two-chain shape identity is the Catalan convolution (DH21 map E7). -/
theorem doubleChain_catalan_convolution (m : ℕ) :
    (∑ j : Fin (m+1), catalan j.val * catalan (m-j.val)) = catalan (m+1) :=
  (catalan_succ m).symm

end WaveTurbulence.Reg
