/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamVertexWeights
public import WaveTurbulenceVineParam.VineParamRungCapTransport
import Mathlib.Tactic

/-! # Endpoint matching for the four replacement rails

The cap permutation may fix or exchange the two inner ports. Its four
endpoint equations are geometric data, independently of all decorations.
-/

public section
namespace WaveTurbulence.Vine.Param
variable {V E : Type*} [DecidableEq V] [AddCommGroup E]

/-- Endpoint support commutes with sums of actual labels. -/
theorem vertexWeight_add (v p : V) (x y : E) :
    vertexWeight v p (x+y)=vertexWeight v p x+vertexWeight v p y := by
  by_cases h : p=v <;> simp [vertexWeight,h]

/-- Endpoint support commutes with differences of actual labels. -/
theorem vertexWeight_sub (v p : V) (x y : E) :
    vertexWeight v p (x-y)=vertexWeight v p x-vertexWeight v p y := by
  by_cases h : p=v <;> simp [vertexWeight,h]

/-- Endpoint support commutes with additive negation. -/
theorem vertexWeight_neg (v p : V) (x : E) :
    vertexWeight v p (-x)= -vertexWeight v p x := by
  by_cases h : p=v <;> simp [vertexWeight,h]

/-- Endpoint support commutes with integral source signs. -/
theorem vertexWeight_zsmul (v p : V) (s : ℤ) (x : E) :
    vertexWeight v p (s • x)=s • vertexWeight v p x := by
  by_cases h : p=v <;> simp [vertexWeight,h]

/-- The actual local source fiber matches both old cut edges after the cap
translation and its prescribed port permutation. The outer ports can coincide. -/
theorem splice_rail_flow_match (P : RungPattern) (σ : V ≃ V)
    (p q c d v : V) (hp : σ p=p) (hq : σ q=q)
    (hc : σ c=if P.reversesPorts then d else c)
    (hd : σ d=if P.reversesPorts then c else d)
    (r before : E) (xy : E×E) :
    P.signs 2 • (vertexWeight (σ v) p (P.upperBefore r before)-vertexWeight (σ v) q before)-
      P.signs 3 • (vertexWeight (σ v) c (P.upperAfter r before xy)-
        vertexWeight (σ v) d (P.lowerAfter before xy))=
    P.signs 2 • (vertexWeight v p (P.upperBefore r before)-
      vertexWeight v c (P.upperBefore r before-P.correction r xy))-
    P.signs 2 • (vertexWeight v q before-vertexWeight v d (before-P.correction r xy)) := by
  have hwp (x : E) : vertexWeight (σ v) p x=vertexWeight v p x := by
    simpa only [hp] using vertexWeight_relabel σ v p x
  have hwq (x : E) : vertexWeight (σ v) q x=vertexWeight v q x := by
    simpa only [hq] using vertexWeight_relabel σ v q x
  cases P
  all_goals simp only [RungPattern.reversesPorts,Bool.false_eq_true,ite_false,ite_true] at hc hd
  all_goals have hwc (x : E) := vertexWeight_relabel σ v c x
  all_goals have hwd (x : E) := vertexWeight_relabel σ v d x
  all_goals simp only [hc,hd] at hwc hwd
  all_goals simp [hwp,hwq,hwc,hwd,RungPattern.signs,RungPattern.upperBefore,
    RungPattern.upperAfter,RungPattern.lowerAfter,RungPattern.correction,
    vertexWeight_add,vertexWeight_sub,vertexWeight_neg]
  all_goals abel

end WaveTurbulence.Vine.Param
