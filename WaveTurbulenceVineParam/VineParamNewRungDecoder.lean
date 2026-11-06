/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamRepresentativeDecoder
import Mathlib.Tactic

/-! # The complete affine integer decoder of both actual inserted rung bonds -/

public section
namespace WaveTurbulence.Vine.Param.RungSpliceGeometry
open Finset
variable {V β ι E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [DecidableEq ι] [Fintype ι] [AddCommGroup E]
variable (G : RungSpliceGeometry V β)

/-- Both fresh double-bond labels have the exact explicit unit decoder
rows in the physical anchored source chart. -/
theorem new_rung_decoder_of_old
    (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b) (g r : E)
    (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchor : Bool)
    (A : β → ι → ℤ) (D : β → ℤ) (href : ∀ e,A e ref= -1)
    (hdecode : ∀ z e,(old.symm z).1 e=g+(∑ i,A e i • z i)+D e • r)
    (x : ι ⊕ Fin 2 → E) (row : Fin 2) :
    ![((G.anchoredInsertionChart a b hab ha hb r old ref anchor).symm x).1 (.inr 2),
      ((G.anchoredInsertionChart a b hab ha hb r old ref anchor).symm x).1 (.inr 3)] row=
      g+(∑ i,insertedRungFree G.pattern anchor row (A G.j) i • x i)+
        insertedRungGap G.pattern anchor row (D G.j) (G.gapSign a b) • r := by
  rw [G.anchoredInsertionChart_decode_labels,G.globalSourceChart_decode]
  change ![(G.pattern.decode
      ((old.symm (G.insertionOldCoordinates a b r ref anchor x)).1 G.j)
      (-x (.inr 0),x (.inr 1))).1,
    (G.pattern.decode ((old.symm (G.insertionOldCoordinates a b r ref anchor x)).1 G.j)
      (-x (.inr 0),x (.inr 1))).2] row=_
  rw [hdecode,G.insertionOldCoordinates_decoder a b r ref anchor (A G.j) (href G.j)]
  have hrail : g+((∑ i,A G.j i • x (.inl i))+
      (if anchor then G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) else 0))+
      D G.j • r=
    g+(∑ i,A G.j i • x (.inl i))+D G.j • r+
      (if anchor then G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) else 0) := by abel
  rw [hrail]
  exact insertedRungFree_eval G.pattern anchor row (A G.j) (D G.j) (G.gapSign a b) g r x

end WaveTurbulence.Vine.Param.RungSpliceGeometry
