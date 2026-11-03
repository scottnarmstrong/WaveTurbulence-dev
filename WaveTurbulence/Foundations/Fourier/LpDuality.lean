/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.LocalizedDuality
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic

/-!
# `Lᵖ` duality by exhaustion of finite-dimensional real spaces

The local dual-power test bounds every compact-ball restriction. Fatou's
lemma then controls the full norm without assuming in advance that the
function belongs to `L^q`.
-/

public section

open MeasureTheory Filter Metric
open scoped ENNReal Topology

namespace WaveTurbulence.Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A bounded measurable function whose `L¹ ∩ Lᵖ` pairings are bounded by `C`
has `L^q` norm at most `C`. No `L^q` membership hypothesis is assumed. -/
theorem eLpNorm_le_of_pairing {p q : ℝ} (hpq : p.HolderConjugate q)
    {f : V → ℂ} (hf : Measurable f) {M : ℝ} (hfM : ∀ x, ‖f x‖ ≤ M)
    {C : ℝ} (hC : 0 ≤ C)
    (htest : ∀ g : V → ℂ, Integrable g → MemLp g (ENNReal.ofReal p) →
      ‖∫ x, f x * g x‖ ≤ C * lpNorm g (ENNReal.ofReal p) volume) :
    eLpNorm f (ENNReal.ofReal q) ≤ ENNReal.ofReal C := by
  let F := fun n : ℕ => (closedBall (0 : V) (n : ℝ)).indicator f
  have hbound (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal q) ≤ ENNReal.ofReal C :=
    eLpNorm_indicator_le_of_pairing (μ := (volume : Measure V))
      (s := closedBall (0 : V) (n : ℝ)) hpq hf hfM hC htest measurableSet_closedBall
      ((isCompact_closedBall (0 : V) (n : ℝ)).measure_lt_top (μ := (volume : Measure V))).ne
  have hlim (x : V) : Tendsto (fun n => F n x) atTop (𝓝 (f x)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop N] with n hn
    apply Set.indicator_of_mem
    simp only [mem_closedBall, dist_zero_right]
    exact hN.trans (by exact_mod_cast hn)
  have hFatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (μ := (volume : Measure V))
    (p := ENNReal.ofReal q) (f := F)
    (fun n => (hf.indicator measurableSet_closedBall).aestronglyMeasurable)
    f hf.aestronglyMeasurable (ae_of_all _ hlim)
  exact hFatou.trans (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hbound))

end WaveTurbulence.Fourier
