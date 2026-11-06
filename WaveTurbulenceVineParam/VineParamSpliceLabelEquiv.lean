/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSixLabelFiber
import Mathlib.Tactic

/-! # Exact insertion/contraction bijection of all local and uncut labels -/

public section
namespace WaveTurbulence.Vine.Param
variable {β R E : Type*} [DecidableEq β] [Fintype β] [AddCommGroup E]

/-- Translating the entire cap is an invertible shear depending on the two
new differences. Every old occurrence is retained individually. -/
@[expose] def spliceLabelShear (P : RungPattern) (r : E) (inside : R → Bool) :
    ((R → E)×(E×(E×E))) ≃ (((R → E)×E)×(E×E)) where
  toFun := fun q => ((fun e => q.1 e+(if inside e then P.correction r q.2.2 else 0),q.2.1),q.2.2)
  invFun := fun q => (fun e => q.1.1 e-(if inside e then P.correction r q.2 else 0),(q.1.2,q.2))
  left_inv := by
    intro q
    apply Prod.ext
    · funext e
      exact add_sub_cancel_right _ _
    · rfl
  right_inv := by
    intro q
    apply Prod.ext
    · apply Prod.ext
      · funext e
        exact sub_add_cancel _ _
      · rfl
    · rfl

/-- A complete inserted-label assignment is equivalent to the complete old
cut-label assignment and exactly two new differences. This is a bijection
of actual labels, not only an injective parametrization. -/
@[expose] def spliceLabelEquiv (i j : β) (hij : i ≠ j) (P : RungPattern) (r : E)
    (inside : {e : β // e ≠ i ∧ e ≠ j} → Bool) :
    (({e : β // e ≠ i ∧ e ≠ j} → E)×SixLabelFiber P r) ≃
      (CutLabelFiber i j P r×(E×E)) :=
  (Equiv.prodCongr (Equiv.refl _) (sixLabelChart P r)).trans
    ((spliceLabelShear P r inside).trans
      (Equiv.prodCongr (cutLabelChart i j hij P r).symm (Equiv.refl _)))

omit [Fintype β] in
/-- Insertion subtracts the same correction from every uncut cap label. -/
theorem spliceLabelEquiv_decode_rest (i j : β) (hij : i ≠ j) (P : RungPattern) (r : E)
    (inside : {e : β // e ≠ i ∧ e ≠ j} → Bool) (q : CutLabelFiber i j P r×(E×E))
    (e : {e : β // e ≠ i ∧ e ≠ j}) :
    ((spliceLabelEquiv i j hij P r inside).symm q).1 e=
      q.1.1 e.1-(if inside e then P.correction r q.2 else 0) := rfl

omit [Fintype β] in
/-- The inverse recovers all six local labels by the physical decoder. -/
theorem spliceLabelEquiv_decode_local (i j : β) (hij : i ≠ j) (P : RungPattern) (r : E)
    (inside : {e : β // e ≠ i ∧ e ≠ j} → Bool) (q : CutLabelFiber i j P r×(E×E)) :
    ((spliceLabelEquiv i j hij P r inside).symm q).2.1=
      spliceChartLabels P r (q.1.1 j) q.2 := rfl

omit [Fintype β] in
/-- The two new free coordinates are fixed differences of actual local labels. -/
theorem spliceLabelEquiv_encode (i j : β) (hij : i ≠ j) (P : RungPattern) (r : E)
    (inside : {e : β // e ≠ i ∧ e ≠ j} → Bool)
    (q : ({e : β // e ≠ i ∧ e ≠ j} → E)×SixLabelFiber P r) :
    (spliceLabelEquiv i j hij P r inside q).2=
      P.encode (q.2.1 1) (q.2.1 2,q.2.1 3) := rfl

end WaveTurbulence.Vine.Param
