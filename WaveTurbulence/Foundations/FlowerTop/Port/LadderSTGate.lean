/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTParam
public import WaveTurbulence.Foundations.Spine.Final4c
/-! # FLOWER-P5: the gate `WTPrefix LadderFourierAtST'`

Copy-and-thread of `ladderFourier_prefix` (`Final4c`); the box length bound is `D + 1`, so the small-parameter
choice uses `τ* + 1` in place of `τ*` (`D δ = τ*`, `δ ≤ 1`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder Filter Topology
open scoped Classical ENNReal

theorem ladderFourierST_prefix : WTPrefix LadderFourierAtST' := by
  intro d hd γ hγ
  refine ⟨1, one_pos, fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  have hd1 : 1 ≤ d := by omega
  refine ⟨C1star d, one_le_C1star hd1, 1, one_pos, fun ν hν => ?_⟩
  have hν0 : 0 < ν := hν.1
  refine ⟨min 1 ((1 / (2 * (τstar + 1))) ^ (1 / (5 * ν))), by have := hτ; have := hν0; positivity,
    fun δ hδ D hD hτD => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hsmall := delta_small (τ := τstar + 1) (by linarith) hν0 hδ0 (hδ.2.trans (min_le_right _ _))
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp (eventually_conditions d γ δ ν hγ.1 hδ0 hν0)
  refine ⟨1, le_rfl, max L1 2, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨h3, h20, hbig, hlog, hΛLam, hfree⟩ := hL1 L (le_trans (le_max_left _ _) hL)
  have hLpos : 0 < L := by linarith
  have hs : 0 < δ ^ (5 * ν) := Real.rpow_pos_of_pos hδ0 _
  apply ladder_fourier_paramST
  refine ⟨hd1, hLpos, hδ0, hδ1, hν0.le, by linarith, hbig, Y_bound (by linarith) h20 hd1, ?_, hΛLam, hfree,
    le_refl _, one_le_C1star hd1⟩
  -- the exponential estimate
  show Real.exp (((D : ℝ) + 1) * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ L ^ (δ ^ (5 * ν))
  have hDδ : (D : ℝ) * δ = τstar := hτD.symm
  have h1 : ((D : ℝ) + 1) * δ ^ (1 + 10 * ν) ≤ δ ^ (5 * ν) / 2 := by
    have e : ((D : ℝ) + 1) * δ ^ (1 + 10 * ν) = (((D : ℝ) + 1) * δ) * δ ^ (10 * ν) := by
      rw [Real.rpow_add hδ0, Real.rpow_one]; ring
    have hle : ((D : ℝ) + 1) * δ ≤ τstar + 1 := by nlinarith
    rw [e]
    refine le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) ?_
    clear e
    have e2 : δ ^ (10 * ν) = δ ^ (5 * ν) * δ ^ (5 * ν) := by
      rw [← Real.rpow_add hδ0]; ring_nf
    rw [e2]
    calc (τstar + 1) * (δ ^ (5 * ν) * δ ^ (5 * ν)) = ((τstar + 1) * δ ^ (5 * ν)) * δ ^ (5 * ν) := by ring
      _ ≤ (1 / 2) * δ ^ (5 * ν) := by gcongr
      _ = _ := by ring
  have hΛ0 : 0 ≤ Real.log L := by linarith
  have h2 : Real.exp (((D : ℝ) + 1) * δ ^ (1 + 10 * ν) * Real.log L) ≤ L ^ (δ ^ (5 * ν) / 2) := by
    rw [Real.rpow_def_of_pos hLpos]
    apply Real.exp_le_exp.mpr
    calc ((D : ℝ) + 1) * δ ^ (1 + 10 * ν) * Real.log L ≤ (δ ^ (5 * ν) / 2) * Real.log L := by gcongr
      _ = Real.log L * (δ ^ (5 * ν) / 2) := by ring
  calc Real.exp (((D : ℝ) + 1) * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4)
      ≤ L ^ (δ ^ (5 * ν) / 2) * L ^ (δ ^ (5 * ν) / 2) := by
        exact mul_le_mul h2 hlog (by positivity) (by positivity)
    _ = L ^ (δ ^ (5 * ν)) := by rw [← Real.rpow_add hLpos]; ring_nf

end WaveTurbulence.FlowerP5
