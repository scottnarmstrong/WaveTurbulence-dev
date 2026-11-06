/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamFullInsertedCoefficients
public import WaveTurbulenceVineParam.VineParamAnchoredPhases
import Mathlib.Tactic

/-! # The explicit integer rows decode all physical rail representatives -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [Fintype ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- The new full integer row for a retained rail representative evaluates
to its actual physical label in the reanchored source chart. -/
theorem representative_decoder_of_old
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchor : Bool)
    (A : β → ι → ℤ) (D : β → ℤ) (href : ∀ e,A e ref= -1)
    (hdecode : ∀ z e,(old.symm z).1 e=g+(∑ i,A e i • z i)+D e • r)
    (x : ι ⊕ Fin 2 → E) (e : β) (side : Bool) (hside : G.AdmissibleSide e side) :
    ((G.anchoredInsertionChart a b hab ha hb r old ref anchor).symm x).1 (G.representative e side)=
      g+(∑ i,insertedRestFree G.pattern anchor side (A e) i • x i)+
        insertedRestGap G.pattern anchor side (D e) (G.gapSign a b) • r := by
  rw [G.anchoredInsertionChart_representative_of_decoder a b hab ha hb g r old ref anchor A D href hdecode x e side hside]
  have h := insertedRestFree_eval G.pattern anchor side (A e) (D e) (G.gapSign a b) r x
  change (∑ i,insertedRestFree G.pattern anchor side (A e) i • x i)+
      insertedRestGap G.pattern anchor side (D e) (G.gapSign a b) • r=
    (∑ i,A e i • x (.inl i))+D e • r+capGauge anchor side •
      G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) at h
  calc
    _=g+((∑ i,insertedRestFree G.pattern anchor side (A e) i • x i)+
      insertedRestGap G.pattern anchor side (D e) (G.gapSign a b) • r) := by rw [h]; abel
    _=_ := by abel

end WaveTurbulence.Vine.Param.RungSpliceGeometry
