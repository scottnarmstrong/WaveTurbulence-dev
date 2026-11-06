/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedFourier
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Pi
/-! Absolute integrability of the literal compactly supported spliced time integrand. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset

 theorem measurableSet_splicedTimeDomain {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ)
    (rootTime : Fin w → ℝ) :
    MeasurableSet (splicedTimeDomain G layer rootTime) := by
  unfold splicedTimeDomain
  measurability

 theorem integrable_splicedFourierIntegrand {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (α : GBranch G.tree → ℝ) :
    Integrable ((splicedTimeDomain G layer rootTime).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))) := by
  let box : Set (GBranch G.tree → ℝ) := Set.pi Set.univ (fun v => Icc (layer v : ℝ) (layer v + 1))
  have hm : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hc : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
  have hb : Integrable (box.indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff hm).mpr (integrableOn_const hc.measure_lt_top.ne)
  have hphase : Continuous (fun t : GBranch G.tree → ℝ =>
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I)) := by fun_prop
  apply hb.mono' (hphase.aestronglyMeasurable.indicator (measurableSet_splicedTimeDomain G layer rootTime))
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : t ∈ splicedTimeDomain G layer rootTime
  · have htbox : t ∈ box := fun v _ => ht.1 v
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem htbox, norm_prod]
    exact (Finset.prod_eq_one (fun _ _ => Complex.norm_exp_ofReal_mul_I _)).le
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

end WaveTurbulence.LGSpine
