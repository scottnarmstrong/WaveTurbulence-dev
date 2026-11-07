/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSubrealization
import Mathlib.Tactic

/-! # The initial double pair inside Figure 3D3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD336FirstEmbedding : Fin AppbPatternKind.d33.pattern.edges.length ↪
    Fin AppbPatternKind.d33new.pattern.edges.length where
  toFun := fun i => ⟨i.val,by have hi := i.isLt; change i.val < 4 at hi; change i.val < 9; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin AppbPatternKind.d33new.pattern.edges.length => x.val) h

noncomputable def appbD336FirstPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern) :
    AppbRealization M AppbPatternKind.d33.pattern :=
  r.subrealization AppbPatternKind.d33.pattern (by decide) (by decide) appbD336FirstEmbedding
    (by decide) (by decide)

end WaveTurbulence.Mole
