/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBClosedSide
import Mathlib.Tactic

/-! # Joint component restrictions determine all physical labels -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem appbSideLabelsPair_injective {K : Type*} (M : Molecule V D) (S : Finset V) :
    Function.Injective (fun κ : D → K =>
      (appbSideLabels M S κ,appbSideLabels M (M.atoms \ S) κ)) := by
  intro κ κ' he
  funext x
  by_cases hx : M.atom x ∈ S
  · exact congrFun (congrArg Prod.fst he) ⟨x,hx⟩
  · exact congrFun (congrArg Prod.snd he) ⟨x,mem_sdiff.mpr ⟨M.atom_mem x,hx⟩⟩

end WaveTurbulence.Mole
