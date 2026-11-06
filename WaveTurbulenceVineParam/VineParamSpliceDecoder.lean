/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamAnchoredInsertion
import Mathlib.Tactic

/-! # Actual inverse labels of the full source insertion chart -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- The full inverse source map retains all old uncut labels with the exact
cap correction, and reconstructs all six local labels without division. -/
theorem globalSourceChart_decode (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (k : DirectedRootFiber G.ends a b r) (xy : E×E) :
    ((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1=
      rungSpliceLabels G.i G.j
        (fun e => k.1 e.1-(if (G.ends e.1).1 ∈ G.cap then
          G.pattern.correction (spliceGap G.cap a b r) xy else 0))
        (spliceChartLabels G.pattern (spliceGap G.cap a b r) (k.1 G.j) xy) := by
  have h : ((G.globalSourceChart a b hab ha hb r).symm (k,xy)).1=
      rungSpliceLabels G.i G.j
        (fun e => k.1 e.1-(if G.inside e then
          G.pattern.correction (spliceGap G.cap a b r) xy else 0))
        (spliceChartLabels G.pattern (spliceGap G.cap a b r) (k.1 G.j) xy) := rfl
  simpa only [inside,decide_eq_true_eq] using h

/-- The anchored inverse is the preceding exact decoder evaluated at its
explicit old-coordinate shear and normalized new-coordinate sign. -/
theorem anchoredInsertionChart_decode_labels {ι : Type*} [DecidableEq ι]
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool)
    (x : ι ⊕ Fin 2 → E) :
    ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1=
      ((G.globalSourceChart a b hab ha hb r).symm
        (old.symm (G.insertionOldCoordinates a b r ref anchorInside x),
          (-x (.inr 0),x (.inr 1)))).1 := by
  apply congrArg Subtype.val
  apply (G.globalSourceChart a b hab ha hb r).injective
  rw [G.anchoredInsertionChart_decode,Equiv.apply_symm_apply]

end WaveTurbulence.Vine.Param.RungSpliceGeometry
