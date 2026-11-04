/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSpines

/-! # Concatenating regular chains (DH21 Propositions 4.5 and 4.10)

Concatenation extends the lone end. It is the normalization needed when the
terminal couple in a type-2 representation is itself of type 2.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Append one chain at another's lone end, retaining every side couple. -/
def appendChain : RegChain → RegChain → RegChain
  | .nil, Y => Y
  | .pair m r g i s, Y => .pair m r g i (appendChain s Y)

/-- Extending global addresses composes by path concatenation. -/
theorem addrExt_append {w : ℕ} (a : Fin w × Path) (p q : Path) :
    addrExt (addrExt a p) q = addrExt a (p ++ q) := by
  change (a.1, (a.2 ++ p) ++ q) = (a.1, a.2 ++ (p ++ q))
  rw [List.append_assoc]

/-- The two continuation slots of a mini-tree preserve the original sign. -/
theorem slotSign_lone (m : MiniTreeCode) (ζ : ℤˣ) : slotSign (slotSign ζ m.c) m.lone = ζ := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [MiniTreeCode.lone, slotSign]

theorem appendChain_lonePath (X Y : RegChain) :
    (appendChain X Y).lonePath = X.lonePath ++ Y.lonePath := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [appendChain, RegChain.lonePath, appendChain_lonePath s, List.append_assoc]
termination_by structural X

/-- Chain concatenation is composition of actual tree contexts. -/
theorem appendChain_plug (X Y : RegChain) (ζ : ℤˣ) (h : TTree) :
    (appendChain X Y).plug ζ h = X.plug ζ (Y.plug ζ h) := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [appendChain, RegChain.plug, appendChain_plug s]
    apply congrArg node3
    funext j
    by_cases hj : j = m.c
    · simp only [hj, ite_true]
      apply congrArg (i.plug (slotSign ζ m.c))
      apply congrArg node3
      funext k
      by_cases hk : k = m.lone
      · subst k
        simp only [ite_true, slotSign_lone]
      · simp only [hk, ite_false]
    · simp only [hj, ite_false]
termination_by structural X

/-- Chain concatenation preserves all source pairs, shifted to the actual lone address. -/
theorem appendChain_pairsAt {w : ℕ} (X Y : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (appendChain X Y).pairsAt ζ a =
      X.pairsAt ζ a ++ Y.pairsAt ζ (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [appendChain, RegChain.pairsAt, RegChain.lonePath, addrExt]
  | pair m r g i s =>
    simp only [appendChain, RegChain.pairsAt, appendChain_pairsAt s, slotSign_lone,
      RegChain.lonePath, addrExt_append, List.append_assoc]
termination_by structural X

/-- Concatenation adds the orders of its two chains. -/
theorem appendChain_size (X Y : RegChain) :
    (appendChain X Y).size = X.size + Y.size := by
  cases X with
  | nil => simp [appendChain, RegChain.size]
  | pair m r g i s =>
    simp only [appendChain, RegChain.size, appendChain_size s]
    omega
termination_by structural X

/-- Concatenation retains well-formed side couples and chain partitions. -/
theorem appendChain_wf (X Y : RegChain) :
    (appendChain X Y).wf = (X.wf && Y.wf) := by
  cases X with
  | nil => simp [appendChain, RegChain.wf]
  | pair m r g i s =>
    simp only [appendChain, RegChain.wf, appendChain_wf s, Bool.and_assoc]
termination_by structural X

/-- An appended chain is empty precisely when both factors are empty. -/
theorem appendChain_isNil (X Y : RegChain) :
    (appendChain X Y).isNil = (X.isNil && Y.isNil) := by
  cases X <;> simp [appendChain, RegChain.isNil]

/-- Concatenating three contexts is independent of parenthesization. -/
theorem appendChain_assoc (X Y Z : RegChain) :
    appendChain (appendChain X Y) Z = appendChain X (appendChain Y Z) := by
  cases X with
  | nil => rfl
  | pair m r g i s => simp only [appendChain, appendChain_assoc s]
termination_by structural X

end WaveTurbulence.Reg
