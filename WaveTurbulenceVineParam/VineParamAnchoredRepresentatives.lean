/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceRepresentatives
public import WaveTurbulenceVineParam.VineParamAnchoredRestDecoder
import Mathlib.Tactic

/-! # Exact affine decoder for every retained physical representative -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [Fintype ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- Any admissible actual representative keeps the old affine decoder
with the source cap/reference correction. In particular this covers all
four replacement rails, on both sides of the marked cut. -/
theorem anchoredInsertionChart_representative_of_decoder
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool)
    (A : β → ι → ℤ) (D : β → ℤ) (href : ∀ e,A e ref= -1)
    (hdecode : ∀ z e,(old.symm z).1 e=g+(∑ i,A e i • z i)+D e • r)
    (x : ι ⊕ Fin 2 → E) (e : β) (side : Bool) (hside : G.AdmissibleSide e side) :
    ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x).1 (G.representative e side)=
      g+(∑ i,A e i • x (.inl i))+D e • r+
        capGauge anchorInside side •
          G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) := by
  rw [G.anchoredInsertionChart_decode_labels]
  let z := G.insertionOldCoordinates a b r ref anchorInside x
  let xy := (-x (.inr 0),x (.inr 1))
  have hrep := G.representative_label a b hab ha hb r (old.symm z) xy e side hside
  have hn := eq_sub_iff_add_eq.mpr hrep.symm
  change ((G.globalSourceChart a b hab ha hb r).symm (old.symm z,xy)).1 (G.representative e side)=_
  rw [hn,hdecode]
  change g+(∑ i,A e i • G.insertionOldCoordinates a b r ref anchorInside x i)+D e • r-
    (if side then G.pattern.correction (spliceGap G.cap a b r) xy else 0)=_
  rw [G.insertionOldCoordinates_decoder a b r ref anchorInside (A e) (href e)]
  cases anchorInside <;> cases side
  all_goals simp [capGauge]
  all_goals abel

end WaveTurbulence.Vine.Param.RungSpliceGeometry
