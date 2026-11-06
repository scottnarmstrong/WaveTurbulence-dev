/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceObservable
import Mathlib.Tactic

/-! # Exact old-atom resonance transport through a rung insertion -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq β] [InnerProductSpace ℝ E] in
/-- Negative molecular Gamma is the negative source incidence observable
of the squared actual labels. -/
theorem directedEnergy_eq_neg_flow (ends : β → V×V) (v : V) (k : β → E) :
    directedEnergy ends v k= -directedFlow ends v (fun e => ‖k e‖^2) := by
  simp only [directedEnergy,directedFlow,zsmul_eq_mul,Int.cast_neg,neg_mul,
    sum_neg_distrib,neg_neg]

omit [InnerProductSpace ℝ E] in
/-- Replacing the two cut occurrences and translating/reflection of the
cap preserves every old source row up to its ordinary uniform translation.
The hypotheses concern endpoints and the old labels, not a chart conclusion. -/
theorem splice_energy_transport (ends : β → V×V) (i j : β) (hij : i ≠ j)
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
    directedEnergy (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v))
      (rungSpliceLabels i j
        (fun e => k e.1-(if (ends e.1).1 ∈ C then P.correction r xy else 0))
        (spliceChartLabels P r before xy))=
      directedEnergy ends v (fun e => k e-(if v ∈ C then P.correction r xy else 0)) := by
  have h := splice_observable_transport ends i j hij σ p q c d v P C hp hq hc hd
    hσp hσq hσc hσd hi hj hrest k r before xy hki hkj (fun x => ‖x‖^2)
  rw [directedEnergy_eq_neg_flow,directedEnergy_eq_neg_flow]
  apply congrArg Neg.neg
  convert h using 1
  apply congrArg (directedFlow _ _)
  funext e
  cases e <;> rfl

end WaveTurbulence.Vine.Param
