/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairGain
import Mathlib.Tactic

/-! # `PairGainInput` (DH23 L1965, Lemma A.3(4)) for `γ > 1/2`

Both branches: the `(3,4)` double bond (G6's five-label count) and the `(3,3)` single bond (A23-HALF
`system12345_bound`, `γ > 1/2`), each followed by the removal of the pair (`Δχ = −3`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem pairGainAt {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    {C1 : ℝ} (hC1 : 0 < C1) (η : ℝ) :
    ∃ K B R : ℝ, ∀ L ≥ R, PairGainAt.{u, v} d L γ δ η C1 K B := by
  obtain ⟨C4, R4, hC4, h4⟩ := pairGain34.{u, v} hd (γ := γ) ⟨by linarith [hγ.1], hγ.2⟩
  obtain ⟨C3, hC3, h3⟩ := pairGain33.{u, v} hd hγ
  obtain ⟨R3, h3'⟩ := h3 δ hδ
  refine ⟨max ((C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) ((C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3),
    8, max (max R4 R3) (Real.exp 1), fun L hL => ?_⟩
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hl8 : Real.log L ^ (8 : ℝ) = Real.log L ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  intro V D _ _ _ M hcap hloop a ha b hb hab hda hcases hconnM hconnP P hP
  unfold AFree
  rw [hl8]
  have hnn : 0 ≤ Real.log L ^ 8 * L ^ (-min γ (1 - γ)) := by
    have := Real.rpow_nonneg hLp.le (-min γ (1 - γ)); positivity
  have h4L : max R4 (Real.exp 1) ≤ L := max_le ((le_max_left _ _).trans ((le_max_left _ _).trans hL)) hLe
  have h3L : max R3 (Real.exp 1) ≤ L := max_le ((le_max_right _ _).trans ((le_max_left _ _).trans hL)) hLe
  rcases hcases with ⟨hdb, hbb⟩ | ⟨hdb, hbb⟩
  · refine (h4 δ hδ C1 hC1 L h4L M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc (C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 * L ^ (-min γ (1 - γ))
        = ((C4 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * (Real.log L ^ 8 * L ^ (-min γ (1 - γ))) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (Real.log L ^ 8)]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  · refine (h3' C1 hC1 L h3L M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP).trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc (C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 * L ^ (-min γ (1 - γ))
        = ((C3 * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * (Real.log L ^ 8 * L ^ (-min γ (1 - γ))) := by ring
      _ ≤ _ := by
        rw [mul_assoc _ (Real.log L ^ 8)]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hnn

/-- **`PairGainInput`** (DH23 L1965, Lemma A.3(4)), for `γ > 1/2`. -/
theorem pairGainInput {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ1 : γ < 1) : PairGainInput.{u, v} d γ η := fun hγ =>
  ⟨1, le_rfl, fun C1 hC1 δ hδ => pairGainAt.{u, v} hd ⟨hγ, hγ1⟩ hδ (by linarith) η⟩

end WaveTurbulence.FinalCountG8
