/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceDecoder
import Mathlib.Tactic

/-! # Exact affine decoder transport for every uncut actual bond

This conditional composition helper consumes a previously proved old
decoder. It is not the source full-vine existence theorem.
-/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [Fintype ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- Reference shear adds one uniform cap correction to an old decoder
whose coefficient on the physical reference is -1. -/
theorem insertionOldCoordinates_decoder (a b : V) (r : E) (ref : ι) (anchorInside : Bool)
    (A : ι → ℤ) (href : A ref= -1) (x : ι ⊕ Fin 2 → E) :
    (∑ i,A i • G.insertionOldCoordinates a b r ref anchorInside x i)=
      (∑ i,A i • x (.inl i))+(if anchorInside then
        G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) else 0) :=
  referenceShear_decoder G.pattern anchorInside ref (spliceGap G.cap a b r) A href
    ((fun i => x (.inl i)),(-x (.inr 0),x (.inr 1)))

/-- Every uncut actual label keeps the old affine decoder and gains exactly
its ternary cap/reference correction. No new free-coordinate sums overlap. -/
theorem anchoredInsertionChart_rest_of_decoder
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool)
    (A : β → ι → ℤ) (D : β → ℤ) (href : ∀ e,A e ref= -1)
    (hdecode : ∀ z e,(old.symm z).1 e=g+(∑ i,A e i • z i)+D e • r)
    (x : ι ⊕ Fin 2 → E) (e : {e : β // e ≠ G.i ∧ e ≠ G.j}) :
    ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1 (.inl e)=
      g+(∑ i,A e.1 i • x (.inl i))+D e.1 • r+
        capGauge anchorInside (G.inside e) •
          G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) := by
  rw [G.anchoredInsertionChart_decode_labels,G.globalSourceChart_decode]
  change (old.symm (G.insertionOldCoordinates a b r ref anchorInside x)).1 e.1-
    (if (G.ends e.1).1 ∈ G.cap then
      G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) else 0)=_
  rw [hdecode,G.insertionOldCoordinates_decoder a b r ref anchorInside (A e.1) (href e.1)]
  cases anchorInside <;> by_cases he : (G.ends e.1).1 ∈ G.cap
  all_goals simp [capGauge,inside,he]
  all_goals abel

end WaveTurbulence.Vine.Param.RungSpliceGeometry
