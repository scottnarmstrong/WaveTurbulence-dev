/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.FlowerTop.Port.CoarseBlockST
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas
public import WaveTurbulence.Foundations.Flower.FinalMKCrude.Fibre
public import WaveTurbulence.Foundations.Flower.FinalMKFine.LBPin

/-! # C2 FINALMK-CRUDE: the marked spliced kernel is bounded by a time-L¹ norm over the free clocks

Copy-thread of Port's `splicedKernelST_norm_le` (itself a copy-thread of main's `splicedKernel_norm_le`) to the
marked kernel `splicedKernelMK`: arbitrary pins `fix`, and the atom weight `atomW`. Ruling R187: the time domain is
intersected with the constant lower bounds `D.lb`; it stays inside the free box, so the bound is unchanged. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKCrude
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.CoarseSpliced WaveTurbulence.FlowerP5
  Finset MeasureTheory Set
open WaveTurbulence.Flower.MkDefs (SplicedKernelDataMK splicedKernelMK splicedTimeIntegralMK splicedLBDomain)
open scoped Classical

variable {w d : ℕ} {G : Garden w}

theorem splicedKernelMK_norm_le (D : SplicedKernelDataMK G d) {L : ℝ} (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (Zsupp : Finset (GenDecoration G d roots 0))
    (hZ : ∀ z : GenDecoration G d roots 0,
      splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 ≠ 0 → z ∈ Zsupp) :
    ‖splicedKernelMK G D L γ η δ base roots‖ ≤
      ‖(coupling d L γ δ : ℂ)‖ ^ G.order *
        ∫ τ in freeBox G D.layer D.fix,
          ‖∑ z ∈ Zsupp, D.atomW (cosetDecoration G L base z.1) *
            (splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 *
              globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ))‖ := by
  set C : Set ({b : GBranch G.tree // D.fix b = none} → ℝ) :=
    G.extendFix D.fix ⁻¹' (splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb) with hC
  have hCm : MeasurableSet C :=
    measurable_extendFix D.fix ((measurableSet_splicedTimeDomainFix G D.layer D.rootTime D.fix).inter
      (FinalMKFine.measurableSet_splicedLBDomain D.lb))
  have hCsub : C ⊆ freeBox G D.layer D.fix := by
    intro τ hτ v _
    have := hτ.1.1 v.1 v.2
    rw [extendFix_free D.fix τ v.1 v.2] at this
    exact this.1
  have hg : ∀ z : GNode G.tree → (Fin d → ℤ), Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
      globalPhase D.toSplicedKernelData L γ δ base z (G.extendFix D.fix τ)) :=
    fun z => (continuous_globalPhase D.toSplicedKernelData L γ δ base z).comp (continuous_extendFix D.fix)
  have hT : ∀ z : GNode G.tree → (Fin d → ℤ), splicedTimeIntegralMK G D L γ δ base z =
      ∫ τ, C.indicator (fun τ => globalPhase D.toSplicedKernelData L γ δ base z (G.extendFix D.fix τ)) τ := by
    intro z
    unfold splicedTimeIntegralMK
    congr 1
    funext τ
    by_cases h : τ ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show G.extendFix D.fix τ ∈
        splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb from h)]
      exact phaseProd_mul_freq D.toSplicedKernelData L γ δ base z _
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show G.extendFix D.fix τ ∉
        splicedTimeDomainFix G D.layer D.rootTime D.fix ∩ splicedLBDomain D.lb from h)]
  have hsum : splicedKernelMK G D L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order * ∑ z ∈ Zsupp,
        (D.atomW (cosetDecoration G L base z.1) *
          splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1) *
          ∫ τ, C.indicator (fun τ => globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) τ := by
    unfold splicedKernelMK
    congr 1
    have hterm : ∀ z : GenDecoration G d roots 0,
        D.atomW (cosetDecoration G L base z.1) *
        (splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegralMK G D L γ δ base z.1 =
        (D.atomW (cosetDecoration G L base z.1) *
          splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1) *
          splicedTimeIntegralMK G D L γ δ base z.1 := by
      intro z
      unfold splicedMomentumAmplitude
      ring
    simp_rw [hterm]
    rw [tsum_eq_sum (s := Zsupp)]
    · refine Finset.sum_congr rfl (fun z _ => ?_)
      rw [← hT z.1]
    · intro z hz
      have h0 : splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 = 0 := by
        by_contra h; exact hz (hZ z h)
      rw [h0, mul_zero, zero_mul]
  rw [hsum, norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hnorm := LadderDecay.norm_sum_integral_indicator_le volume Zsupp
    (fun z => D.atomW (cosetDecoration G L base z.1) *
      splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1)
    (fun z τ => globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) C
    (freeBox G D.layer D.fix) hCm hCsub ?_ ?_
  · simpa only [mul_assoc] using hnorm
  · intro z _
    exact ((hg z.1).continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)).mono_set hCsub
      |> fun h => (integrable_indicator_iff hCm).mpr h
  · have hc : Continuous (fun τ : {b : GBranch G.tree // D.fix b = none} → ℝ =>
        ∑ z ∈ Zsupp, (D.atomW (cosetDecoration G L base z.1) *
          splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1) *
          globalPhase D.toSplicedKernelData L γ δ base z.1 (G.extendFix D.fix τ)) :=
      continuous_finsetSum _ (fun z _ => continuous_const.mul (hg z.1))
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_freeBox G D.layer D.fix)

end WaveTurbulence.Flower.FinalMKCrude
