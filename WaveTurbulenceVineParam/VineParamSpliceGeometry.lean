/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCutPrecedingGap
public import WaveTurbulenceVineParam.VineParamSpliceEnergyTransport
import Mathlib.Tactic

/-! # Geometric input and exact conservation transport for one rung

The data refer only to the finite directed graph, the marked cap and its
permutation. No chart, decoder, resonance or decoration is a field.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- Source geometric data at a balanced two-edge cap. -/
structure RungSpliceGeometry (V β : Type*) [DecidableEq V] [Fintype β] [DecidableEq β] where
  ends : β → V×V
  i : β
  j : β
  distinct : i ≠ j
  pattern : RungPattern
  cap : Finset V
  p : V
  q : V
  c : V
  d : V
  outer_p : p ∉ cap
  outer_q : q ∉ cap
  inner_c : c ∈ cap
  inner_d : d ∈ cap
  σ : V ≃ V
  fixed_p : σ p=p
  fixed_q : σ q=q
  port_c : σ c=if pattern.reversesPorts then d else c
  port_d : σ d=if pattern.reversesPorts then c else d
  first : ends i=orientPair (pattern.signs 2) p c
  second : ends j=orientPair (-pattern.signs 2) q d
  uncut : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ cap ↔ (ends e).2 ∈ cap)
  preserves_cap : ∀ v,σ v ∈ cap ↔ v ∈ cap
  balanced : ∀ v,(∑ e,-energySign ends v e)=0

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- The actual inserted graph, with individual old bond occurrences retained. -/
@[expose] def newEnds := rungSpliceEnds G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern

/-- Uncut label memberships are selected before decorations. -/
@[expose] def inside (e : {e : β // e ≠ G.i ∧ e ≠ G.j}) : Bool := decide ((G.ends e.1).1 ∈ G.cap)

/-- The exact full local label bijection specialized to this cap. -/
@[expose] def labelEquiv {E : Type*} [AddCommGroup E] (r : E) :=
  spliceLabelEquiv G.i G.j G.distinct G.pattern r G.inside

/-- Assemble the remaining actual bonds and all six local labels. -/
@[expose] def labels {E : Type*} [AddCommGroup E] {r : E}
    (q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern r) :=
  rungSpliceLabels G.i G.j q.1 q.2.1

/-- Full old-atom momentum is preserved by the inverse local chart. Balanced
source degree removes its only possible uniform-translation correction. -/
theorem decode_flow {E : Type*} [AddCommGroup E] (r : E)
    (q : CutLabelFiber G.i G.j G.pattern r×(E×E)) (v : V) :
    directedFlow G.newEnds (.inl (G.σ v)) (G.labels ((G.labelEquiv r).symm q))=
      directedFlow G.ends v q.1.1 := by
  change directedFlow (rungSpliceEnds G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern)
    (.inl (G.σ v)) (rungSpliceLabels G.i G.j
      (fun e => q.1.1 e.1-(if G.inside e then G.pattern.correction r q.2 else 0))
      (spliceChartLabels G.pattern r (q.1.1 G.j) q.2))=_
  simp only [inside,decide_eq_true_eq]
  rw [splice_flow_transport G.ends G.i G.j G.distinct G.σ G.p G.q G.c G.d v G.pattern
    G.cap G.outer_p G.outer_q G.inner_c G.inner_d G.fixed_p G.fixed_q G.port_c G.port_d
    G.first G.second G.uncut q.1.1 r (q.1.1 G.j) q.2 q.1.2 rfl]
  simp only [sub_eq_add_neg,directedFlow_translate,G.balanced,zero_zsmul,add_zero]

/-- After contraction, every old source row has exactly its former value. -/
theorem encode_flow {E : Type*} [AddCommGroup E] (r : E)
    (q : ({e : β // e ≠ G.i ∧ e ≠ G.j} → E)×SixLabelFiber G.pattern r) (v : V) :
    directedFlow G.newEnds (.inl (G.σ v)) (G.labels q)=
      directedFlow G.ends v (G.labelEquiv r q).1.1 := by
  have h := G.decode_flow r (G.labelEquiv r q) v
  simpa only [Equiv.symm_apply_apply] using h

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
