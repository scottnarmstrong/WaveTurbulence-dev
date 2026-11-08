/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Gate
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the deliverables

- `ladderFourierMKFace_prefix : WTPrefix LadderFourierAtMKFace` (D7's face export, F-C0-14);
- `ladderFourierMK_prefix : WTPrefix LadderFourierAtMK` (its `face ≡ none` case);
- `ladderFourierAt_of_MK` (in `Bridge`), and as a check `ladderFourierGate_viaMK : LadderFourierGate`.

The parameter choices are Port's `ladderFourierST_prefix` (box length `D + 1`, so `τ* + 1` in the small-δ choice),
with `C₁ = 2·C1star d` and `256` in the large-`L` condition `free`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open Filter Topology
open scoped Classical ENNReal

/-- Monotonicity of the parameter prefix. -/
theorem wtPrefix_mono {Q Q' : WTParams → Prop} (h : WTPrefix Q) (hQ : ∀ P, Q P → Q' P) : WTPrefix Q' := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := h d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφ τ hτ φ hW => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, H⟩ := H η hη φin hφ τ hτ φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H⟩ := H ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H⟩ := H δ hδ D hD hτD
  exact ⟨C₂, hC₂, L₀, hL₀, fun L hL => hQ _ (H L hL)⟩

/-- The constant `C₁`. -/
noncomputable def C1MK (d : ℕ) : ℝ := 2 * C1star d

theorem one_le_C1MK {d : ℕ} (hd : 1 ≤ d) : 1 ≤ C1MK d := by
  unfold C1MK; have := one_le_C1star hd; linarith

theorem C1MK_ge (d : ℕ) : 256 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1MK d := by
  unfold C1MK C1star; nlinarith

theorem eventually_conditionsMK (d : ℕ) (γ δ ν : ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (hν : 0 < ν) :
    ∀ᶠ L : ℝ in atTop, 3 ≤ L ∧ 20 ≤ Real.log L ∧ Real.log L ^ 2 < 1 + δ * L ^ (2 * γ) ∧
      (Real.log L) ^ (2 * d + 4) ≤ L ^ (δ ^ (5 * ν) / 2) ∧ (Real.log L) ^ 2 ≤ L ^ (δ ^ (5 * ν)) ∧
      256 * (180 * d * Real.log L) ≤ L ^ (δ ^ (5 * ν)) := by
  have hs : 0 < δ ^ (5 * ν) := Real.rpow_pos_of_pos hδ _
  filter_upwards [eventually_conditions d γ δ ν hγ hδ hν,
    eventually_log_pow_le 1 (256 * 180 * d) (δ ^ (5 * ν)) (by positivity) hs]
    with L hc h6
  obtain ⟨h3, h20, h2, h4, h5, -⟩ := hc
  refine ⟨h3, h20, h2, h4, h5, ?_⟩
  calc 256 * (180 * d * Real.log L) = 256 * 180 * d * (Real.log L) ^ 1 := by ring
    _ ≤ _ := h6

/-- **`WTPrefix LadderFourierAtMKFace`** (o73 Prop 18.1: pins and endpoint substitutions). -/
theorem ladderFourierMKFace_prefix : WTPrefix LadderFourierAtMKFace := by
  intro d hd γ hγ
  refine ⟨1, one_pos, fun η hη φin hφin τstar hτ φ hφ => ?_⟩
  have hd1 : 1 ≤ d := by omega
  refine ⟨C1MK d, one_le_C1MK hd1, 1, one_pos, fun ν hν => ?_⟩
  have hν0 : 0 < ν := hν.1
  refine ⟨min 1 ((1 / (2 * (τstar + 1))) ^ (1 / (5 * ν))), by have := hτ; have := hν0; positivity,
    fun δ hδ D hD hτD => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 := hδ.2.trans (min_le_left _ _)
  have hsmall := delta_small (τ := τstar + 1) (by linarith) hν0 hδ0 (hδ.2.trans (min_le_right _ _))
  obtain ⟨L1, hL1⟩ := eventually_atTop.mp (eventually_conditionsMK d γ δ ν hγ.1 hδ0 hν0)
  refine ⟨1, le_rfl, max L1 2, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨h3, h20, hbig, hlog, hΛLam, hfree⟩ := hL1 L (le_trans (le_max_left _ _) hL)
  have hLpos : 0 < L := by linarith
  have hs : 0 < δ ^ (5 * ν) := Real.rpow_pos_of_pos hδ0 _
  apply ladder_fourier_paramMK
  refine ⟨hd1, hLpos, hδ0, hδ1, hν0.le, by linarith, hbig, Y_bound (by linarith) h20 hd1, ?_, hΛLam, hfree,
    C1MK_ge d, one_le_C1MK hd1⟩
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

/-- **`WTPrefix LadderFourierAtMK`** (o73 Prop 18.1, pins only). -/
theorem ladderFourierMK_prefix : WTPrefix LadderFourierAtMK :=
  wtPrefix_mono ladderFourierMKFace_prefix ladderFourierAtMK_of_face

/-- Check: the pinned gate gives main's ladder Fourier gate through the bridge. -/
theorem ladderFourierGate_viaMK : LadderFourierGate :=
  wtPrefix_mono ladderFourierMK_prefix ladderFourierAt_of_MK

end WaveTurbulence.Flower.FinalMKPin
