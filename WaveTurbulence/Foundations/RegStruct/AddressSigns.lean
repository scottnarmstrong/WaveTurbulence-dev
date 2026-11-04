/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.ChainSpines
public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-! # Sign transport through chain spines and mini-tree slots (DH21 Proposition 4.7) -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Appending a path transports its node sign from the actual global root. -/
theorem nodeSign_addrExt {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (p : Path) :
    nodeSign σ (addrExt a p) = pathSign (nodeSign σ a) p :=
  Comb.pathSign_append (σ a.1) a.2 p

/-- Literal slot signs agree with the source's path sign. -/
theorem pathSign_singleton (ζ : ℤˣ) (j : Fin 3) : pathSign ζ [j] = slotSign ζ j := by
  fin_cases j <;> simp [pathSign, slotSign]

/-- Global child signs are the mini-tree slot signs. -/
theorem nodeSign_step {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (j : Fin 3) :
    nodeSign σ (addrExt a [j]) = slotSign (nodeSign σ a) j := by
  rw [nodeSign_addrExt, pathSign_singleton]

/-- A full nested chain transports its original sign to the lone slot. -/
theorem nodeSign_spine {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path) (X : RegChain) :
    nodeSign σ (addrExt a X.lonePath) = nodeSign σ a := by
  rw [nodeSign_addrExt, lonePath_sign]

/-- Passing through a nested inner chain preserves the lower branch's slot signs. -/
theorem nodeSign_chain_child {w : ℕ} (σ : Fin w → ℤˣ) (a : Fin w × Path)
    (X : RegChain) (c j : Fin 3) :
    nodeSign σ (addrExt a ([c] ++ X.lonePath ++ [j])) =
      slotSign (slotSign (nodeSign σ a) c) j := by
  rw [← addrExt_append, nodeSign_step, ← addrExt_append, nodeSign_spine, nodeSign_step]

/-- Red endpoints of any of the six mini-trees have opposite signs. -/
theorem slotSign_red (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.red.2 = -slotSign ζ m.red.1 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [slotSign, MiniTreeCode.red]

/-- Green endpoints of any of the six mini-trees have opposite signs. -/
theorem slotSign_green (m : MiniTreeCode) (ζ : ℤˣ) :
    slotSign (slotSign ζ m.c) m.green.2 = -slotSign ζ m.green.1 := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> simp [slotSign, MiniTreeCode.green]

end WaveTurbulence.Reg
