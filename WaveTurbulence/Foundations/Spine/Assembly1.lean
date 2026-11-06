/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FibreFactor
public import WaveTurbulence.Foundations.Spine.Support
public import WaveTurbulence.Foundations.Spine.BlockInt
/-! # The spliced kernel is bounded by the time-L1 norm of its integrand sum (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset MeasureTheory Set
open scoped Classical

variable {w d : ℕ} {G : Garden w}

theorem continuous_globalPhase (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : Continuous (globalPhase D L γ δ base z) := by
  unfold globalPhase
  refine continuous_finsetProd _ (fun v _ => ?_)
  fun_prop

theorem splicedKernel_norm_le (D : SplicedKernelData G d) {L : ℝ} (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (Zsupp : Finset (GenDecoration G d roots 0))
    (hZ : ∀ z : GenDecoration G d roots 0, splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 → z ∈ Zsupp) :
    ‖splicedKernel G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ G.order *
        ∫ t in ubox (fun v : GBranch G.tree => (D.layer v : ℝ)),
          ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t‖ := by
  have hsum : splicedKernel G D L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order * ∑ z ∈ Zsupp, splicedMomentumAmplitude G D L γ η base z.1 *
        ∫ t, (splicedTimeDomain G D.layer D.rootTime).indicator (globalPhase D L γ δ base z.1) t := by
    unfold splicedKernel
    congr 1
    rw [tsum_eq_sum (s := Zsupp)]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [splicedTimeIntegral_eq_fourierB]
      rfl
    · intro z hz
      have h0 : splicedMomentumAmplitude G D L γ η base z.1 = 0 := by
        by_contra h; exact hz (hZ z h)
      unfold splicedMomentumAmplitude at h0
      rw [h0, zero_mul]
  rw [hsum, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_sum_integral_indicator_le volume Zsupp (fun z => splicedMomentumAmplitude G D L γ η base z.1)
    (fun z t => globalPhase D L γ δ base z.1 t) (splicedTimeDomain G D.layer D.rootTime)
    (ubox (fun v : GBranch G.tree => (D.layer v : ℝ))) (measurableSet_splicedTimeDomain G D.layer D.rootTime) ?_
    (fun z _ => integrable_splicedFourierIntegrand G D.layer D.rootTime _) ?_
  · intro t ht v _
    exact (ht.1 v)
  · have hc : Continuous (fun t : GBranch G.tree → ℝ =>
        ∑ z ∈ Zsupp, splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul (continuous_globalPhase D L γ δ base z.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_ubox _)

end WaveTurbulence.CoarseSpliced
