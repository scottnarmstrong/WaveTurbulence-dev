/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-! # Canonical terminal-couple normalization (DH21 Proposition 4.10)

A type-2 terminal couple is absorbed into the two outer chains. Empty outer
chains are removed. Both trees and the actual unordered pair relation are
preserved; no source regularity characterization is assumed.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Attach two outer chains, omitting the redundant type-2 constructor when both are empty. -/
def joinChains (Xp Xm : RegChain) (Q : RegCpl) : RegCpl :=
  if Xp.isNil && Xm.isNil then Q else .type2 Xp Xm Q

/-- Absorb all terminal type-2 structure into the two outer chains. -/
def attachChains (Xp Xm : RegChain) : RegCpl → RegCpl
  | .type2 Yp Ym Q => attachChains (appendChain Xp Yp) (appendChain Xm Ym) Q
  | Q => joinChains Xp Xm Q

/-- The reduced outer constructor represents the same actual pair of trees. -/
theorem joinChains_trees (Xp Xm : RegChain) (Q : RegCpl) :
    (joinChains Xp Xm Q).trees = (Xp.plug 1 Q.trees.1, Xm.plug (-1) Q.trees.2) := by
  cases Xp <;> cases Xm <;> simp [joinChains, RegChain.isNil, RegCpl.trees, RegChain.plug]

/-- The reduced outer constructor preserves the actual unordered leaf-pair relation. -/
theorem mem_joinChains_pairsAt {w : ℕ} (Xp Xm : RegChain) (Q : RegCpl)
    (a b : Fin w × Path) (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (joinChains Xp Xm Q).pairsAt a b ↔
      z ∈ Xp.pairsAt 1 a ∨ z ∈ Xm.pairsAt (-1) b ∨
      z ∈ Q.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := by
  cases Xp <;> cases Xm <;>
    simp [joinChains, RegChain.isNil, RegChain.pairsAt, RegChain.lonePath,
      RegCpl.pairsAt, addrExt, List.mem_append, or_assoc]

/-- Terminal normalization retains every original pair, even when list order changes. -/
theorem mem_attachChains_pairsAt {w : ℕ} (Xp Xm : RegChain) (Q : RegCpl)
    (a b : Fin w × Path) (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (attachChains Xp Xm Q).pairsAt a b ↔
      z ∈ Xp.pairsAt 1 a ∨ z ∈ Xm.pairsAt (-1) b ∨
      z ∈ Q.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := by
  cases Q with
  | triv => exact mem_joinChains_pairsAt _ _ _ _ _ _
  | type1 c r g d => exact mem_joinChains_pairsAt _ _ _ _ _ _
  | type2 Yp Ym q =>
    rw [attachChains, mem_attachChains_pairsAt]
    simp only [appendChain_pairsAt, appendChain_lonePath, RegCpl.pairsAt,
      List.mem_append, addrExt_append]
    tauto
termination_by structural Q

/-- The outer-constructor reduction enforces both uniqueness side conditions. -/
theorem joinChains_wf (Xp Xm : RegChain) (Q : RegCpl)
    (hp : Xp.wf = true) (hm : Xm.wf = true) (hq : Q.wf = true) (ht : Q.isType2 = false) :
    (joinChains Xp Xm Q).wf = true := by
  cases Xp <;> cases Xm <;>
    simp_all only [joinChains, RegChain.isNil, Bool.and_false,
      Bool.and_true, Bool.false_eq_true, ↓reduceIte, RegCpl.wf,
      Bool.not_false]

/-- Canonical attachment always returns well-formed data when its inputs are well formed. -/
theorem attachChains_wf (Xp Xm : RegChain) (Q : RegCpl)
    (hp : Xp.wf = true) (hm : Xm.wf = true) (hq : Q.wf = true) :
    (attachChains Xp Xm Q).wf = true := by
  cases Q with
  | triv => exact joinChains_wf _ _ _ hp hm hq rfl
  | type1 c a b d => exact joinChains_wf _ _ _ hp hm hq rfl
  | type2 Yp Ym q =>
    simp only [RegCpl.wf, Bool.and_eq_true] at hq
    apply attachChains_wf _ _ q
    · rw [appendChain_wf, hp, hq.1.1.1.1]
      rfl
    · rw [appendChain_wf, hm, hq.1.1.1.2]
      rfl
    · exact hq.1.1.2
termination_by structural Q

end WaveTurbulence.Reg
