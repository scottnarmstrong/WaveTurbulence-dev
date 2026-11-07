/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Assembly1
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas
/-! # FLOWER-P5: the spliced kernel with stubs is bounded by the time-L1 norm over the FREE clocks

Copy-and-thread of the coarse provider's `Assembly1` (`splicedKernel_norm_le`): the integral runs over the
free branches (`D.fix b = none`) with the stubs at `D.stubTime`; the box is the unit box of the free branches. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.CoarseSpliced Finset MeasureTheory Set
open scoped Classical

variable {w d : ℕ} {G : Garden w}

/-- The unit box of the free branches. -/
def freeBox (G : Garden w) (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ) :
    Set ({b : GBranch G.tree // fix b = none} → ℝ) :=
  Set.pi univ (fun v => Icc (layer v.1 : ℝ) (layer v.1 + 1))

theorem isCompact_freeBox (G : Garden w) (layer : GBranch G.tree → ℕ) (fix : GBranch G.tree → Option ℝ) :
    IsCompact (freeBox G layer fix) := isCompact_univ_pi (fun _ => isCompact_Icc)

theorem phaseProd_mul_freq (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (t : GBranch G.tree → ℝ) :
    phaseProd L γ δ G (cosetDecoration G L base z) t *
      ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I) =
    globalPhase D L γ δ base z t := by
  unfold phaseProd globalPhase
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro v _
  rw [← Complex.exp_add]
  congr 1
  unfold splicedFrequency
  push_cast
  ring

theorem splicedKernelST_norm_le (D : SplicedKernelDataST G d) {L : ℝ} (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (Zsupp : Finset (GenDecoration G d roots 0))
    (hZ : ∀ z : GenDecoration G d roots 0,
      splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 ≠ 0 → z ∈ Zsupp) :
    ‖splicedKernelST G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ G.order *
        ∫ τ in freeBox G D.layer D.fix,
          ‖∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 *
            globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)‖ := by
  set C : Set ({b : GBranch G.tree // D.fix b = none} → ℝ) :=
    G.extendFix D.fix ⁻¹' splicedTimeDomainFix G D.layer D.rootTime D.fix with hC
  have hCm : MeasurableSet C :=
    measurable_extendFix D.fix (measurableSet_splicedTimeDomainFix G D.layer D.rootTime D.fix)
  have hCsub : C ⊆ freeBox G D.layer D.fix := by
    intro τ hτ v _
    have := hτ.1 v.1 v.2
    rw [extendFix_free D.fix τ v.1 v.2] at this
    exact this.1
  have hg : ∀ z : GNode G.tree → (Fin d → ℤ), Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      globalPhase D.toSplicedKernelData L γ δ base z (G.extendFix D.fix τ)) :=
    fun z => (continuous_globalPhase D.toSplicedKernelData L γ δ base z).comp (continuous_extendFix D.fix)
  have hT : ∀ z : GNode G.tree → (Fin d → ℤ), splicedTimeIntegralST G D L γ δ base z =
      ∫ τ, C.indicator (fun τ => globalPhase D.toSplicedKernelData L γ δ base z (G.extendFix D.fix τ)) τ := by
    intro z
    unfold splicedTimeIntegralST
    congr 1
    funext τ
    by_cases h : τ ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show G.extendFix D.fix τ ∈
        splicedTimeDomainFix G D.layer D.rootTime D.fix from h)]
      exact phaseProd_mul_freq D.toSplicedKernelData L γ δ base z _
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show G.extendFix D.fix τ ∉
        splicedTimeDomainFix G D.layer D.rootTime D.fix from h)]
  have hsum : splicedKernelST G D L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order * ∑ z ∈ Zsupp,
        splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 *
          ∫ τ, C.indicator (fun τ => globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) τ := by
    unfold splicedKernelST splicedKernelSX
    congr 1
    rw [tsum_eq_sum (s := Zsupp)]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← hT z.1, one_mul]
      rfl
    · intro z hz
      have h0 : splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 = 0 := by
        by_contra h; exact hz (hZ z h)
      unfold splicedMomentumAmplitude at h0
      rw [one_mul, h0, zero_mul]
  rw [hsum, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine LadderDecay.norm_sum_integral_indicator_le volume Zsupp
    (fun z => splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1)
    (fun z τ => globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) C
    (freeBox G D.layer D.fix) hCm hCsub ?_ ?_
  · intro z _
    exact ((hg z.1).continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)).mono_set hCsub
      |> fun h => (integrable_indicator_iff hCm).mpr h
  · have hc : Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
        ∑ z ∈ Zsupp, splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 *
          globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul (hg z.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)

end WaveTurbulence.FlowerP5
