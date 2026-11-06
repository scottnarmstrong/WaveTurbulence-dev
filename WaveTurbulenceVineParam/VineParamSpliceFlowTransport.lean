/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamGraphSpliceOldFlow
public import WaveTurbulenceVineParam.VineParamSpliceRailMatching
public import WaveTurbulenceVineParam.VineParamCapTranslation
public import WaveTurbulenceVineParam.VineParamTwoEdgeDecomposition
import Mathlib.Tactic

/-! # Exact old-vertex conservation transport through one rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β] [AddCommGroup E]

/-- All six local labels reconstructed from the two actual new differences. -/
@[expose] def spliceChartLabels (P : RungPattern) (r before : E) (xy : E×E) : Fin 6 → E :=
  ![P.upperBefore r before,before,(P.decode before xy).1,(P.decode before xy).2,
    P.upperAfter r before xy,P.lowerAfter before xy]

/-- At a cut edge the uniform shift at its atom affects just its cap endpoint. -/
theorem oriented_cut_flow_shift (s : ℤ) (hs : s=1 ∨ s= -1)
    (C : Finset V) (p c v : V) (hp : p ∉ C) (hc : c ∈ C) (k t : E) :
    (-energySign (fun _ : Unit => orientPair s p c) v ()) • (k-(if v ∈ C then t else 0))=
      s • (vertexWeight v p k-vertexWeight v c (k-t)) := by
  rw [flow_orientedPair s hs]
  rw [vertexWeight_cap_shift,vertexWeight_cap_shift]
  simp only [hp,hc,ite_false,ite_true,sub_zero]

omit [DecidableEq β] in
/-- Source flow in the cut-free remainder sees a uniform translation at its atom. -/
theorem capSubtract_flow (ends : β → V×V) (C : Finset V)
    (hC : ∀ e,(ends e).1 ∈ C ↔ (ends e).2 ∈ C) (k : β → E) (t : E) (v : V) :
    directedFlow ends v (fun e => k e-(if (ends e).1 ∈ C then t else 0))=
      directedFlow ends v (fun e => k e-(if v ∈ C then t else 0)) := by
  have h := capTranslate_flow ends C hC k (-t) v
  rw [← directedFlow_translate] at h
  change directedFlow ends v (fun e => k e+(if (ends e).1 ∈ C then -t else 0))=
    directedFlow ends v (fun e => k e+(if v ∈ C then -t else 0)) at h
  simpa only [sub_eq_add_neg,neg_ite,neg_zero] using h

/-- Replacing the two cut occurrences and translating/reflection of the
cap preserves every old source row up to its ordinary uniform translation.
The hypotheses concern endpoints and the old labels, not a chart conclusion. -/
theorem splice_flow_transport (ends : β → V×V) (i j : β) (hij : i ≠ j)
    (σ : V ≃ V) (p q c d v : V) (P : RungPattern) (C : Finset V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hσp : σ p=p) (hσq : σ q=q)
    (hσc : σ c=if P.reversesPorts then d else c)
    (hσd : σ d=if P.reversesPorts then c else d)
    (hi : ends i=orientPair (P.signs 2) p c)
    (hj : ends j=orientPair (-P.signs 2) q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (k : β → E) (r before : E) (xy : E×E)
    (hki : k i=P.upperBefore r before) (hkj : k j=before) :
    directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v))
      (rungSpliceLabels i j
        (fun e => k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0))
        (spliceChartLabels P r before xy))=
      directedFlow ends v (fun e => k e-(if v ∈ C then P.correction r xy else 0)) := by
  have hs : P.signs 2=1 ∨ P.signs 2= -1 := by cases P <;> decide
  have hns : -P.signs 2=1 ∨ -P.signs 2= -1 := by omega
  rw [rungSpliceFlow_old]
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
    (k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0)))+
    P.signs 2 • (vertexWeight (σ v) p (P.upperBefore r before)-vertexWeight (σ v) q before)-
    P.signs 3 • (vertexWeight (σ v) c (P.upperAfter r before xy)-
      vertexWeight (σ v) d (P.lowerAfter before xy))=_
  rw [add_sub_assoc]
  rw [splice_rail_flow_match P σ p q c d v hσp hσq hσc hσd]
  have hr := capSubtract_flow (fun e : {e : β // e ≠ i ∧ e ≠ j} => ends e.1) C
    (fun e => hrest e.1 e.2.1 e.2.2) (fun e => k e.1) (P.correction r xy) v
  change directedFlow _ _ _=directedFlow _ _ _ at hr
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
    (k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0)))=
    (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
      (k e.1-(if v ∈ C then P.correction r xy else 0))) at hr
  rw [hr]
  unfold directedFlow
  rw [sum_two_edge_rest i j hij]
  have hfi := oriented_cut_flow_shift (P.signs 2) hs C p c v hp hc (k i) (P.correction r xy)
  have hfj := oriented_cut_flow_shift (-P.signs 2) hns C q d v hq hd (k j) (P.correction r xy)
  simp only [energySign,hi,hj] at hfi hfj ⊢
  rw [hfi,hfj,hki,hkj]
  simp only [neg_smul]
  abel

end WaveTurbulence.Vine.Param
