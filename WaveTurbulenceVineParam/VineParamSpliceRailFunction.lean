/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceRailMatching
import Mathlib.Tactic

/-! # Matching replacement rail labels under arbitrary endpoint observables -/

public section
namespace WaveTurbulence.Vine.Param
variable {V E A : Type*} [DecidableEq V] [AddCommGroup E] [AddCommGroup A]

/-- Rail matching is pointwise in labels, hence applies also to their squared
norms. No linearity of the observable is required. -/
theorem splice_rail_observable_match (P : RungPattern) (σ : V ≃ V)
    (p q c d v : V) (hp : σ p=p) (hq : σ q=q)
    (hc : σ c=if P.reversesPorts then d else c)
    (hd : σ d=if P.reversesPorts then c else d)
    (r before : E) (xy : E×E) (f : E → A) :
    P.signs 2 • (vertexWeight (σ v) p (f (P.upperBefore r before))-vertexWeight (σ v) q (f before))-
      P.signs 3 • (vertexWeight (σ v) c (f (P.upperAfter r before xy))-
        vertexWeight (σ v) d (f (P.lowerAfter before xy)))=
    P.signs 2 • (vertexWeight v p (f (P.upperBefore r before))-
      vertexWeight v c (f (P.upperBefore r before-P.correction r xy)))-
    P.signs 2 • (vertexWeight v q (f before)-vertexWeight v d (f (before-P.correction r xy))) := by
  have hwp (x : A) : vertexWeight (σ v) p x=vertexWeight v p x := by
    simpa only [hp] using vertexWeight_relabel σ v p x
  have hwq (x : A) : vertexWeight (σ v) q x=vertexWeight v q x := by
    simpa only [hq] using vertexWeight_relabel σ v q x
  have hports := P.cap_ports_match r before xy
  cases P
  all_goals simp only [RungPattern.reversesPorts,Bool.false_eq_true,ite_false,ite_true] at hc hd hports
  all_goals have hwc (x : A) := vertexWeight_relabel σ v c x
  all_goals have hwd (x : A) := vertexWeight_relabel σ v d x
  all_goals simp only [hc,hd] at hwc hwd
  all_goals rw [eq_sub_iff_add_eq.mpr hports.1,eq_sub_iff_add_eq.mpr hports.2]
  all_goals simp [hwp,hwq,hwc,hwd,RungPattern.signs]
  all_goals abel

end WaveTurbulence.Vine.Param
