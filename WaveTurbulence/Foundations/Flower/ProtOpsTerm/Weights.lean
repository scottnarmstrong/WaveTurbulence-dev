/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Split
public import WaveTurbulence.Foundations.Fourier.TimeWeights

/-! # PROT-OPS-TERM: the time weight of a concatenated frequency -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

theorem tb_append_le {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeBracket (Fin.append a b) ≤ max (timeBracket a) (timeBracket b) := by
  apply timeBracket_le ((one_le_timeBracket a).trans (le_max_left _ _))
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · rw [Fin.append_left]; exact (bracket_le_timeBracket a i).trans (le_max_left _ _)
  · rw [Fin.append_right]; exact (bracket_le_timeBracket b i).trans (le_max_right _ _)

theorem tb_left_le {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeBracket a ≤ timeBracket (Fin.append a b) := by
  apply timeBracket_le (one_le_timeBracket _)
  intro j
  have := bracket_le_timeBracket (Fin.append a b) (Fin.castAdd m j)
  rwa [Fin.append_left] at this

theorem tb_right_le {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeBracket b ≤ timeBracket (Fin.append a b) := by
  apply timeBracket_le (one_le_timeBracket _)
  intro j
  have := bracket_le_timeBracket (Fin.append a b) (Fin.natAdd n j)
  rwa [Fin.append_right] at this

theorem tw_left_le {n m : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeWeight θ a ≤ timeWeight θ (Fin.append a b) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (timeBracket_pos _).le (tb_left_le a b) hθ)

theorem tw_right_le {n m : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeWeight θ b ≤ timeWeight θ (Fin.append a b) :=
  ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (timeBracket_pos _).le (tb_right_le a b) hθ)

theorem tw_append_le {n m : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (a : Fin n → ℝ) (b : Fin m → ℝ) :
    timeWeight θ (Fin.append a b) ≤ timeWeight θ a + timeWeight θ b := by
  unfold timeWeight
  have h1 : timeBracket (Fin.append a b) ^ θ ≤ max (timeBracket a ^ θ) (timeBracket b ^ θ) := by
    rcases le_total (timeBracket a) (timeBracket b) with h | h
    · calc _ ≤ timeBracket b ^ θ := Real.rpow_le_rpow (timeBracket_pos _).le
              ((tb_append_le a b).trans (by rw [max_eq_right h])) hθ
        _ ≤ _ := le_max_right _ _
    · calc _ ≤ timeBracket a ^ θ := Real.rpow_le_rpow (timeBracket_pos _).le
              ((tb_append_le a b).trans (by rw [max_eq_left h])) hθ
        _ ≤ _ := le_max_left _ _
  calc ENNReal.ofReal (timeBracket (Fin.append a b) ^ θ)
      ≤ ENNReal.ofReal (max (timeBracket a ^ θ) (timeBracket b ^ θ)) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal (timeBracket a ^ θ + timeBracket b ^ θ) := by
        apply ENNReal.ofReal_le_ofReal
        exact max_le (le_add_of_nonneg_right (Real.rpow_nonneg (timeBracket_pos _).le _))
          (le_add_of_nonneg_left (Real.rpow_nonneg (timeBracket_pos _).le _))
    _ = _ := ENNReal.ofReal_add (Real.rpow_nonneg (timeBracket_pos _).le _)
          (Real.rpow_nonneg (timeBracket_pos _).le _)

end WaveTurbulence.Flower.ProtOpsTerm
