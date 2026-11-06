/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamRungSource
public import WaveTurbulenceVineParam.VineParamLadderCharts
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-! # Exact parametrization of full source-conserving rung and ladder labels

Each rung carries both actual double-bond labels and its two following rails.
The preceding gap fixes the preceding upper rail. Conservation determines
all the remaining rails, so the chart is a bijection of the whole local
source fiber, not merely a change of two unconstrained input labels.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {E : Type*} [AddCommGroup E]

/-- Actual double-bond labels and following rails satisfying the two source
momentum equations, with the prescribed preceding physical gap. -/
@[expose] def RungFlowFiber (P : RungPattern) (r d : E) :=
  {q : (E×E)×(E×E) //
    P.signs 0 • q.1.1+P.signs 1 • q.1.2+P.signs 3 • q.2.1-
      P.signs 2 • P.upperBefore r d=0 ∧
    P.signs 0 • q.1.1+P.signs 1 • q.1.2+P.signs 3 • q.2.2-P.signs 2 • d=0}

/-- The complete four-label rung fiber has precisely two free difference
coordinates, for every actual orientation and every prescribed gap. -/
@[expose] def rungFiberChart (P : RungPattern) (r d : E) : RungFlowFiber P r d ≃ (E×E) where
  toFun := fun q => P.encode d q.1.1
  invFun := fun xy => ⟨(P.decode d xy,(P.upperAfter r d xy,P.lowerAfter d xy)),P.momentum_additive r d xy⟩
  left_inv := by
    intro q
    apply Subtype.ext
    apply Prod.ext
    · exact P.decode_encode d q.1.1
    · exact Prod.ext (P.upperAfter_of_conservation r q.1.1.1 q.1.1.2 d q.1.2.1 q.2.1)
        (P.lowerAfter_of_conservation q.1.1.1 q.1.1.2 d q.1.2.2 q.2.2)
  right_inv := by
    intro xy
    exact P.encode_decode d xy

/-- A complete sequence of source-conserving rung labels, carrying the actual
following lower rail to the next rung. Direction compatibility of successive
upper rails is supplied separately from the actual shared rail incidence. -/
@[expose] def RungChainFiber (E : Type*) [AddCommGroup E] : List RungPattern → E → E → Type _
  | [],_,_ => PUnit
  | P::ps,r,d => (q : RungFlowFiber P r d) × RungChainFiber E ps r q.1.2.2

/-- All complete rung fibers in an arbitrary ladder are parametrized by one
pair of integral difference coordinates per rung, including the empty case. -/
@[expose] def fullLadderFiberChart : (ps : List RungPattern) → (r d : E) →
    RungChainFiber E ps r d ≃ RungValues E ps
  | [],_,_ => Equiv.refl _
  | P::ps,r,d =>
    (Equiv.sigmaCongrRight (fun q : RungFlowFiber P r d =>
      fullLadderFiberChart ps r q.1.2.2)).trans
      ((Equiv.sigmaEquivProd _ _).trans
        (Equiv.prodCongr (rungFiberChart P r d) (Equiv.refl _)))

end WaveTurbulence.Vine.Param
