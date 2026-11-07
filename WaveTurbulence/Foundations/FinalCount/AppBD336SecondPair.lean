/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBD336FirstPair
public import WaveTurbulence.Foundations.FinalCount.AppBResidualSubrealization
import Mathlib.Tactic

/-! # The actual residual special pair in Figure 3D3New -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbD336ResidualPattern : AppbPattern :=
  ⟨[(3,4),(3,5),(3,5),(4,6),(4,6)],{3,4}⟩

def appbD336SecondEmbedding : Fin appbD336ResidualPattern.edges.length ↪
    Fin AppbPatternKind.d33new.pattern.edges.length where
  toFun := fun i => ⟨i.val+4,by have hi := i.isLt; change i.val < 5 at hi; change i.val+4 < 9; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hh := congrArg (fun x : Fin AppbPatternKind.d33new.pattern.edges.length => x.val) h
    change i.val+4 = j.val+4 at hh
    omega

noncomputable def appbD336SecondPair {M : Molecule V D}
    (r : AppbRealization M AppbPatternKind.d33new.pattern) :
    AppbRealization (appbD336FirstPair r).post appbD336ResidualPattern :=
  r.residualSubrealization {1,2} (by decide) appbD336ResidualPattern (by decide) (by decide)
    (by decide) appbD336SecondEmbedding (by decide) (by decide)

end WaveTurbulence.Mole
