/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceFlowTransport
public import WaveTurbulenceVineParam.VineParamSpliceRailFunction
import Mathlib.Tactic

/-! # One-rung transport for arbitrary actual bond observables -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E A : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [AddCommGroup E] [AddCommGroup A]

omit [Fintype β] [DecidableEq β] in
/-- An observable at an endpoint reads the cap shift of that endpoint. -/
theorem vertexWeight_cap_observable (C : Finset V) (v p : V) (x t : E) (f : E → A) :
    vertexWeight v p (f (x-(if v ∈ C then t else 0)))=
      vertexWeight v p (f (x-(if p ∈ C then t else 0))) := by
  by_cases h : p=v
  · subst p; rfl
  · simp only [vertexWeight,h,ite_false]

omit [Fintype β] [DecidableEq β] in
/-- A cut edge has its unshifted outer and translated inner observable. -/
theorem oriented_cut_observable_shift (s : ℤ) (hs : s=1 ∨ s= -1)
    (C : Finset V) (p c v : V) (hp : p ∉ C) (hc : c ∈ C) (k t : E) (f : E → A) :
    (-energySign (fun _ : Unit => orientPair s p c) v ()) • (f (k-(if v ∈ C then t else 0)))=
      s • (vertexWeight v p (f k)-vertexWeight v c (f (k-t))) := by
  rw [flow_orientedPair s hs]
  rw [vertexWeight_cap_observable,vertexWeight_cap_observable]
  simp only [hp,hc,ite_false,ite_true,sub_zero]

omit [DecidableEq β] in
/-- Uniform component translation is pointwise at every incident atom,
including after a nonlinear observable is applied to each label. -/
theorem capObservable_flow (ends : β → V×V) (C : Finset V)
    (hC : ∀ e,(ends e).1 ∈ C ↔ (ends e).2 ∈ C) (k : β → E) (t : E) (v : V) (f : E → A) :
    directedFlow ends v (fun e => f (k e-(if (ends e).1 ∈ C then t else 0)))=
      directedFlow ends v (fun e => f (k e-(if v ∈ C then t else 0))) := by
  apply sum_congr rfl
  intro e _
  dsimp only
  by_cases hi : (ends e).1=v ∨ (ends e).2=v
  · rcases hi with h | h
    · rw [h]
    · have hm : (ends e).1 ∈ C ↔ v ∈ C := (hC e).trans (by rw [h])
      simp only [hm]
  · have ht := not_or.mp hi
    simp only [energySign,ht.1,ht.2,ite_false,sub_zero,neg_zero,zero_zsmul]

/-- Replacing the two cut occurrences and translating/reflection of the
cap preserves every old source row up to its ordinary uniform translation.
The hypotheses concern endpoints and the old labels, not a chart conclusion. -/
theorem splice_observable_transport (ends : β → V×V) (i j : β) (hij : i ≠ j)
    (σ : V ≃ V) (p q c d v : V) (P : RungPattern) (C : Finset V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hσp : σ p=p) (hσq : σ q=q)
    (hσc : σ c=if P.reversesPorts then d else c)
    (hσd : σ d=if P.reversesPorts then c else d)
    (hi : ends i=orientPair (P.signs 2) p c)
    (hj : ends j=orientPair (-P.signs 2) q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C))
    (k : β → E) (r before : E) (xy : E×E)
    (hki : k i=P.upperBefore r before) (hkj : k j=before) (f : E → A) :
    directedFlow (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v))
      (rungSpliceLabels i j
        (fun e => f (k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0)))
        (fun a => f (spliceChartLabels P r before xy a)))=
      directedFlow ends v (fun e => f (k e-(if v ∈ C then P.correction r xy else 0))) := by
  have hs : P.signs 2=1 ∨ P.signs 2= -1 := by cases P <;> decide
  have hns : -P.signs 2=1 ∨ -P.signs 2= -1 := by omega
  rw [rungSpliceFlow_old]
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
    f (k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0)))+
    P.signs 2 • (vertexWeight (σ v) p (f (P.upperBefore r before))-vertexWeight (σ v) q (f before))-
    P.signs 3 • (vertexWeight (σ v) c (f (P.upperAfter r before xy))-
      vertexWeight (σ v) d (f (P.lowerAfter before xy)))=_
  rw [add_sub_assoc]
  rw [splice_rail_observable_match P σ p q c d v hσp hσq hσc hσd r before xy f]
  have hr := capObservable_flow (fun e : {e : β // e ≠ i ∧ e ≠ j} => ends e.1) C
    (fun e => hrest e.1 e.2.1 e.2.2) (fun e => k e.1) (P.correction r xy) v f
  change directedFlow _ _ _=directedFlow _ _ _ at hr
  change (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
    f (k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0)))=
    (∑ e : {e : β // e ≠ i ∧ e ≠ j},(-energySign ends v e.1) •
      f (k e.1-(if v ∈ C then P.correction r xy else 0))) at hr
  rw [hr]
  unfold directedFlow
  rw [sum_two_edge_rest i j hij]
  have hfi := oriented_cut_observable_shift (P.signs 2) hs C p c v hp hc (k i) (P.correction r xy) f
  have hfj := oriented_cut_observable_shift (-P.signs 2) hns C q d v hq hd (k j) (P.correction r xy) f
  simp only [energySign,hi,hj] at hfi hfj ⊢
  rw [hfi,hfj,hki,hkj]
  simp only [neg_smul]
  abel


end WaveTurbulence.Vine.Param
