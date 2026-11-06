/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamSpliceGlobalFiber
import Mathlib.Tactic

/-! # Exact old-atom resonance law for the full one-rung source chart -/

public section
namespace WaveTurbulence.Vine.Param
open Finset
variable {V β E : Type*} [DecidableEq V] [Fintype β] [DecidableEq β]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq β] in
/-- For balanced source degree, translating all incident labels by -t
changes negative Gamma by twice the source flow paired with t. -/
theorem directedEnergy_sub_of_balanced (ends : β → V×V) (v : V) (k : β → E) (t : E)
    (hbal : (∑ e,-energySign ends v e)=0) :
    directedEnergy ends v (fun e => k e-t)=
      directedEnergy ends v k+2*inner ℝ (directedFlow ends v k) t := by
  have hz : (∑ e,energySign ends v e)=0 := by
    simpa only [sum_neg_distrib,neg_eq_zero] using hbal
  have hr : (∑ e,(energySign ends v e : ℝ))=0 := by
    rw [← Int.cast_sum,hz,Int.cast_zero]
  have hf : (∑ e,(energySign ends v e : ℝ) • k e)= -directedFlow ends v k := by
    simp only [directedFlow,Int.cast_smul_eq_zsmul,neg_smul,sum_neg_distrib,neg_neg]
  change (∑ e,(energySign ends v e : ℝ)*‖k e-t‖^2)=_
  simp only [sub_eq_add_neg]
  rw [signed_energy_translate,hf,hr]
  simp only [inner_neg_left,inner_neg_right,neg_neg,zero_mul,add_zero]
  rfl

namespace RungSpliceGeometry
variable (G : RungSpliceGeometry V β)

/-- The complete source decoder obeys the exact old-atom resonance law.
Interior rows are invariant; joint rows have precisely the reanchoring term. -/
theorem decode_energy (gap : E) (q : CutLabelFiber G.i G.j G.pattern gap×(E×E)) (v : V) :
    directedEnergy G.newEnds (.inl (G.σ v)) (G.labels ((G.labelEquiv gap).symm q))=
      directedEnergy G.ends v q.1.1+
        2*inner ℝ (directedFlow G.ends v q.1.1)
          (if v ∈ G.cap then G.pattern.correction gap q.2 else 0) := by
  change directedEnergy (rungSpliceEnds G.ends G.i G.j G.σ G.p G.q G.c G.d G.pattern)
    (.inl (G.σ v)) (rungSpliceLabels G.i G.j
      (fun e => q.1.1 e.1-(if G.inside e then G.pattern.correction gap q.2 else 0))
      (spliceChartLabels G.pattern gap (q.1.1 G.j) q.2))=_
  simp only [inside,decide_eq_true_eq]
  rw [splice_energy_transport G.ends G.i G.j G.distinct G.σ G.p G.q G.c G.d v G.pattern
    G.cap G.outer_p G.outer_q G.inner_c G.inner_d G.fixed_p G.fixed_q G.port_c G.port_d
    G.first G.second G.uncut q.1.1 gap (q.1.1 G.j) q.2 q.1.2 rfl]
  exact directedEnergy_sub_of_balanced G.ends v q.1.1 _ (G.balanced v)

/-- Interior negative Gamma is unchanged by the complete source insertion. -/
theorem decode_energy_of_zero (gap : E) (q : CutLabelFiber G.i G.j G.pattern gap×(E×E))
    (v : V) (hv : directedFlow G.ends v q.1.1=0) :
    directedEnergy G.newEnds (.inl (G.σ v)) (G.labels ((G.labelEquiv gap).symm q))=
      directedEnergy G.ends v q.1.1 := by
  rw [G.decode_energy,hv,inner_zero_left,mul_zero,add_zero]

end RungSpliceGeometry
end WaveTurbulence.Vine.Param
