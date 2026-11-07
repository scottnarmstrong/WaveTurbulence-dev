/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLSlotOrigins

/-! # The canonical bond representative preserves its actual incidence -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D]

theorem internalDartBond_originAt (M : Molecule V D) (S : Finset V) (b : V) (d : InternalDart M S) :
    OriginAt M S b (.inl (internalDartBond M S d).1) (M.atom d.1) (M.out d.1) := by
  unfold internalDartBond
  split_ifs with ho
  · exact Or.inl ⟨rfl,rfl⟩
  · exact Or.inr ⟨by rw [M.mate_mate],by rw [M.mate_mate]⟩

end WaveTurbulence.VineEstS2
