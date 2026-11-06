/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceDecoder
import Mathlib.Tactic

/-! # Fixed actual-bond origins of the two inserted contract coordinates -/

public section
namespace WaveTurbulence.Vine.Param

/-- Ordered physical origins of (normalized x,y) in the six-label cell. -/
@[expose] def insertedDifferenceOrigins (P : RungPattern) : Fin 2 → Fin 6×Fin 6 :=
  match P with
  | .pp => ![(3,1),(2,1)]
  | .pmForward => ![(3,2),(2,1)]
  | .pmBackward => ![(3,2),(3,1)]
  | .mpForward => ![(2,3),(3,1)]
  | .mpBackward => ![(2,3),(2,1)]
  | .mm => ![(1,3),(2,1)]

/-- Both inserted coordinates are differences of fixed actual cell labels,
with no source or coordinate hypothesis. -/
theorem insertedDifferenceOrigins_eval {E : Type*} [AddCommGroup E] (P : RungPattern)
    (z : Fin 6 → E) (i : Fin 2) :
    ![-(P.encode (z 1) (z 2,z 3)).1,(P.encode (z 1) (z 2,z 3)).2] i=
      z (insertedDifferenceOrigins P i).1-z (insertedDifferenceOrigins P i).2 := by
  cases P <;> fin_cases i <;> simp [insertedDifferenceOrigins,RungPattern.encode,neg_sub]

namespace RungSpliceGeometry
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- The unnormalized new pair in the full source chart is its actual two
local differences, independent of every old label and every reference. -/
theorem globalSourceChart_encode_new (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (k : DirectedRootFiber G.newEnds (.inl a) (.inl b) r) :
    (G.globalSourceChart a b hab ha hb r k).2=
      G.pattern.encode (k.1 (.inr 1)) (k.1 (.inr 2),k.1 (.inr 3)) := rfl

/-- The exact difference-origin field for either newly inserted contract slot. -/
theorem anchoredInsertionChart_difference_new {ι : Type*} [DecidableEq ι]
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool)
    (k : DirectedRootFiber G.newEnds (.inl a) (.inl b) r) (i : Fin 2) :
    G.anchoredInsertionChart a b hab ha hb r old ref anchorInside k (.inr i)=
      k.1 (.inr (insertedDifferenceOrigins G.pattern i).1)-
        k.1 (.inr (insertedDifferenceOrigins G.pattern i).2) := by
  change ![-(G.globalSourceChart a b hab ha hb r k).2.1,
    (G.globalSourceChart a b hab ha hb r k).2.2] i=_
  rw [G.globalSourceChart_encode_new]
  exact insertedDifferenceOrigins_eval G.pattern (fun i => k.1 (.inr i)) i

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
