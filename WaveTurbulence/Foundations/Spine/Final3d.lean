/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3c
import Mathlib.Tactic
/-! The real inequality behind the class condition. -/
@[expose] public section
open Finset MeasureTheory
open scoped ENNReal
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
open scoped Classical
variable {w d : ℕ} {G : Garden w}

theorem lw_small {L γ δ P : ℝ} (h : 1 + δ * L ^ (2 * γ) * P ≤ Real.log L ^ 2) :
    Molecule.ladderWeight L γ δ P = 1 + δ * L ^ (2 * γ) * P := by
  unfold Molecule.ladderWeight; exact min_eq_right h

theorem lw_large {L γ δ P : ℝ} (hP1 : P ≤ 1) (_hP0 : 0 ≤ P) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (_hc : 0 ≤ δ * L ^ (2 * γ)) (h : ¬ (P < 1 ∧ 1 + δ * L ^ (2 * γ) * P ≤ Real.log L ^ 2)) :
    Molecule.ladderWeight L γ δ P = Real.log L ^ 2 := by
  unfold Molecule.ladderWeight
  apply min_eq_left
  by_contra hcon
  have hcon' := not_le.mp hcon
  apply h
  refine ⟨?_, hcon'.le⟩
  rcases hP1.lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hcon'
    linarith

theorem rhoS_le {d : ℕ} {L γ δ P a : ℝ} (ha : a = 1 + d * (2 : ℝ) ^ (d - 1)) (hc : 0 ≤ δ * L ^ (2 * γ))
    (hP0 : 0 ≤ P) (ha1 : 1 ≤ a) :
    rhoS d L γ δ P ≤ 8 * a * (1 + δ * L ^ (2 * γ) * P) := by
  unfold rhoS
  have hpos : 0 ≤ δ * L ^ (2 * γ) * P := mul_nonneg hc hP0
  have h8 : |8 * δ * L ^ (2 * γ) * P| = 8 * (δ * L ^ (2 * γ) * P) := by
    rw [abs_of_nonneg (by nlinarith)]; ring
  rw [h8, ← ha]
  have h2 : 2 + 2 * (d : ℝ) * (2 : ℝ) ^ (d - 1) = 2 * a := by rw [ha]; ring
  generalize δ * L ^ (2 * γ) * P = u
  have e : 8 * a * (1 + u) = a * (8 * u) + 8 * a := by ring
  rw [e]
  linarith [h2, ha1]

theorem combine_real {c P Yv R0 C1 : ℝ} {n m' : ℕ} (hc : c ≤ 4 ^ n) (_hc0 : 0 ≤ c) (hP : 0 ≤ P) (hY : 0 ≤ Yv)
    (harith : P * 128 ^ n * Yv ^ m' ≤ R0) (hC1 : 1 ≤ C1) (hR0 : 0 ≤ R0) :
    c * 8 ^ n * (P * Real.pi ^ n * Yv ^ m') ≤ C1 * R0 := by
  have hπ : Real.pi ^ n ≤ 4 ^ n := pow_le_pow_left₀ Real.pi_pos.le Real.pi_le_four n
  have h1 : c * 8 ^ n * (P * Real.pi ^ n * Yv ^ m') ≤ 4 ^ n * 8 ^ n * (P * 4 ^ n * Yv ^ m') := by
    gcongr
  have h2 : 4 ^ n * 8 ^ n * (P * 4 ^ n * Yv ^ m') = P * 128 ^ n * Yv ^ m' := by
    have : (128 : ℝ) ^ n = 4 ^ n * 8 ^ n * 4 ^ n := by rw [← mul_pow, ← mul_pow]; norm_num
    rw [this]; ring
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ R0 := harith
    _ ≤ C1 * R0 := by nlinarith

end WaveTurbulence.Ladder
