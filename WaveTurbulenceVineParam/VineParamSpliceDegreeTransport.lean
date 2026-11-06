/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceFlowTransport
import Mathlib.Tactic

/-! # Balanced degrees descend through contraction of an actual rung

This uses the local source flow identity at constant integer labels and
does not presuppose balanced degrees of the contracted graph.
-/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]

/-- At zero differences and zero gap, every physical local bond has the
same unit label, in all six source orientation patterns. -/
theorem spliceChartLabels_one (P : RungPattern) :
    spliceChartLabels P (0 : ℤ) 1 (0,0)=fun _ => 1 := by
  funext i
  cases P <;> fin_cases i <;>
    simp [spliceChartLabels,RungPattern.upperBefore,RungPattern.decode,
      RungPattern.upperAfter,RungPattern.lowerAfter]

/-- The ordinary outgoing-minus-incoming degree at an old vertex is
unchanged by the complete reflected source splice. -/
theorem splice_old_degree (ends : β → V×V) (i j : β) (hij : i ≠ j)
    (σ : V ≃ V) (p q c d v : V) (P : RungPattern) (C : Finset V)
    (hp : p ∉ C) (hq : q ∉ C) (hc : c ∈ C) (hd : d ∈ C)
    (hσp : σ p=p) (hσq : σ q=q)
    (hσc : σ c=if P.reversesPorts then d else c)
    (hσd : σ d=if P.reversesPorts then c else d)
    (hi : ends i=orientPair (P.signs 2) p c)
    (hj : ends j=orientPair (-P.signs 2) q d)
    (hrest : ∀ e,e ≠ i → e ≠ j → ((ends e).1 ∈ C ↔ (ends e).2 ∈ C)) :
    (∑ e,-energySign (rungSpliceEnds ends i j σ p q c d P) (.inl (σ v)) e)=
      ∑ e,-energySign ends v e := by
  have hu : P.upperBefore (0 : ℤ) 1=1 := by cases P <;> simp [RungPattern.upperBefore]
  have hz : P.correction (0 : ℤ) (0,0)=0 := by cases P <;> simp [RungPattern.correction]
  have h := splice_flow_transport ends i j hij σ p q c d v P C hp hq hc hd hσp hσq hσc hσd
    hi hj hrest (fun _ => (1 : ℤ)) 0 1 (0,0) hu.symm rfl
  rw [spliceChartLabels_one,hz] at h
  have hk : rungSpliceLabels i j
      (fun e : {e : β // e ≠ i ∧ e ≠ j} => (1 : ℤ)-(if (ends e.1).1 ∈ C then 0 else 0))
      (fun _ => 1)=fun _ => 1 := by
    funext e
    cases e <;> simp [rungSpliceLabels]
  rw [hk] at h
  simpa only [ite_self,sub_zero,directedFlow,smul_eq_mul,mul_one] using h

end WaveTurbulence.Vine.Param
