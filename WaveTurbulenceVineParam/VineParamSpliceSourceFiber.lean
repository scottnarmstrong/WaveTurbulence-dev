/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceGeometry
import Mathlib.Tactic

/-! # Exact one-rung equivalence restricted to the global source rows -/

public section
namespace WaveTurbulence.Vine.Param
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- The source forcing supported at the two actual joint atoms. -/
@[expose] def rootForcing (a b : V) (r : E) (v : V) : E :=
  if v=a then -r else if v=b then r else 0

/-- All actual source conservation equations, including both joints. -/
@[expose] def HasRootFlow (ends : β → V×V) (a b : V) (r : E) (k : β → E) : Prop :=
  ∀ v,directedFlow ends v k=rootForcing a b r v

/-- The full source label fiber, with no coordinate assumptions. -/
@[expose] def DirectedRootFiber (ends : β → V×V) (a b : V) (r : E) :=
  {k : β → E // HasRootFlow ends a b r k}

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- The old source fiber automatically satisfies the local cut condition. -/
theorem source_cut_gap (a b : V) (hab : a ≠ b) (r : E) (k : DirectedRootFiber G.ends a b r) :
    k.1 G.i=G.pattern.upperBefore (spliceGap G.cap a b r) (k.1 G.j) := by
  apply old_cut_preceding_gap G.ends G.i G.j G.distinct G.pattern G.cap G.p G.q G.c G.d
    a b hab G.outer_p G.outer_q G.inner_c G.inner_d G.first G.second G.uncut k.1 r
  · simpa only [rootForcing,ite_true] using k.2 a
  · simpa only [rootForcing,Ne.symm hab,ite_false,ite_true] using k.2 b
  · intro v _ hva hvb
    simpa only [rootForcing,hva,hvb,ite_false] using k.2 v

/-- Adding the cut equation to the actual source fiber loses no labels:
it is a consequence of source conservation. -/
@[expose] def sourceCutChart (a b : V) (hab : a ≠ b) (r : E) :
    DirectedRootFiber G.ends a b r ≃
      {k : CutLabelFiber G.i G.j G.pattern (spliceGap G.cap a b r) // HasRootFlow G.ends a b r k.1} where
  toFun := fun k => ⟨⟨k.1,G.source_cut_gap a b hab r k⟩,k.2⟩
  invFun := fun k => ⟨k.1.1,k.2⟩
  left_inv := by intro k; rfl
  right_inv := by intro k; rfl

/-- The old-atom source equations on a full inserted local assignment.
The two fresh source equations are already part of SixLabelFiber. -/
@[expose] def LocalRootRows (a b : V) (r gap : E)
    (q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern gap) : Prop :=
  ∀ v,directedFlow G.newEnds (.inl (G.σ v)) (G.labels q)=rootForcing a b r v

/-- Actual source rows are preserved in both directions by the complete
insertion/contraction label equivalence. -/
theorem localRootRows_iff (a b : V) (r gap : E)
    (q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern gap) :
    G.LocalRootRows a b r gap q ↔ HasRootFlow G.ends a b r (G.labelEquiv gap q).1.1 := by
  simp only [LocalRootRows,HasRootFlow,G.encode_flow]

/-- Separate the two new free differences from a source-conserving old cut. -/
@[expose] def cutSourceProdChart (a b : V) (r gap : E) :
    {q : CutLabelFiber G.i G.j G.pattern gap×(E×E) // HasRootFlow G.ends a b r q.1.1} ≃
    ({k : CutLabelFiber G.i G.j G.pattern gap // HasRootFlow G.ends a b r k.1}×(E×E)) where
  toFun := fun q => (⟨q.1.1,q.2⟩,q.1.2)
  invFun := fun q => ⟨(q.1.1,q.2),q.1.2⟩
  left_inv := by intro q; rfl
  right_inv := by intro q; rfl

/-- The complete inserted source fiber contributes exactly two independent
actual differences to the complete old source fiber. -/
@[expose] def localSourceChart (a b : V) (hab : a ≠ b) (r : E) :
    {q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern (spliceGap G.cap a b r) //
      G.LocalRootRows a b r (spliceGap G.cap a b r) q} ≃
      (DirectedRootFiber G.ends a b r×(E×E)) :=
  (Equiv.subtypeEquiv (G.labelEquiv (spliceGap G.cap a b r))
    (G.localRootRows_iff a b r (spliceGap G.cap a b r))).trans
      ((G.cutSourceProdChart a b r (spliceGap G.cap a b r)).trans
        (Equiv.prodCongr (G.sourceCutChart a b hab r).symm (Equiv.refl _)))

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
