/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamContractRungSigns
import Mathlib.Tactic

/-! # Combining a source chart with an inserted rung while retaining its reference

This is a chart-composition helper. Concrete source producers must supply
and prove the old chart and its decoder; no full-vine result is asserted here.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {ι V β E : Type*} [DecidableEq ι] [DecidableEq V] [Fintype β] [DecidableEq β]
  [AddCommGroup E]

/-- Put the two new coordinates after the old coordinate index set. -/
@[expose] def insertionFreePack : ((ι → E)×(E×E)) ≃ (ι ⊕ Fin 2 → E) where
  toFun := fun q => Sum.elim q.1 ![q.2.1,q.2.2]
  invFun := fun x => (fun i => x (.inl i),(x (.inr 0),x (.inr 1)))
  left_inv := by intro q; rfl
  right_inv := by
    intro x
    funext i
    cases i with
    | inl i => rfl
    | inr i => fin_cases i <;> rfl

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- Compose a previously constructed source chart with the full insertion
bijection, normalize t/s signs, and retain the actual included-joint reference. -/
@[expose] def anchoredInsertionChart (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool) :
    DirectedRootFiber G.newEnds (.inl a) (.inl b) r ≃ (ι ⊕ Fin 2 → E) :=
  (G.globalSourceChart a b hab ha hb r).trans
    ((Equiv.prodCongr old (Equiv.refl _)).trans
      ((referenceShear G.pattern anchorInside ref (spliceGap G.cap a b r)).trans
        ((Equiv.prodCongr (Equiv.refl _) rungSignEquiv).trans insertionFreePack)))

/-- The old coordinates used by the physical decoder differ only at its
reference slot, by the explicit cap correction. -/
@[expose] def insertionOldCoordinates (a b : V) (r : E) (ref : ι) (anchorInside : Bool)
    (x : ι ⊕ Fin 2 → E) : ι → E :=
  fun i => x (.inl i)-(if i=ref ∧ anchorInside=true then
    G.pattern.correction (spliceGap G.cap a b r) (-x (.inr 0),x (.inr 1)) else 0)

/-- Exact old-fiber and local-coordinate components of the inverse chart. -/
theorem anchoredInsertionChart_decode (a b : V) (hab : a ≠ b) (ha : G.σ a=a) (hb : G.σ b=b)
    (r : E) (old : DirectedRootFiber G.ends a b r ≃ (ι → E)) (ref : ι) (anchorInside : Bool)
    (x : ι ⊕ Fin 2 → E) :
    G.globalSourceChart a b hab ha hb r ((G.anchoredInsertionChart a b hab ha hb r old ref anchorInside).symm x)=
      (old.symm (G.insertionOldCoordinates a b r ref anchorInside x),(-x (.inr 0),x (.inr 1))) := by
  simp only [anchoredInsertionChart,Equiv.symm_trans_apply,Equiv.apply_symm_apply]
  rfl

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
