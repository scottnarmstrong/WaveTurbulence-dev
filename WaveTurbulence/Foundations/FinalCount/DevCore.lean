/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.CutRank
public import WaveTurbulence.Foundations.FinalCount.CutLad5
public import WaveTurbulence.Foundations.FinalCount.BetaCover
/-! Deviations of a cut (FINALCOUNT-G2 step 3): the transfer lemma for `countA` and the ladder-weight facts. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- Transfer of `𝔈 ≤ N 𝔈'` and the real factors to the `ℝ≥0∞`-valued products. -/
theorem countA_dev_of_parts (E1 E2 : ℕ∞) (a1 a2 : ℝ) (Nn : ℕ∞) (c : ℝ) (hc : 0 ≤ c)
    (hE : E1 ≤ Nn * E2) (ha : a1 ≤ c * a2) :
    IsDeviation ((E1 : ℝ≥0∞) * ENNReal.ofReal a1) ((E2 : ℝ≥0∞) * ENNReal.ofReal a2)
      ((Nn : ℝ≥0∞) * ENNReal.ofReal c) := by
  unfold IsDeviation
  have h1 : (E1 : ℝ≥0∞) ≤ (Nn : ℝ≥0∞) * (E2 : ℝ≥0∞) := by
    rw [← ENat.toENNReal_mul]; exact ENat.toENNReal_le.mpr hE
  have h2 : ENNReal.ofReal a1 ≤ ENNReal.ofReal c * ENNReal.ofReal a2 := by
    rw [← ENNReal.ofReal_mul hc]; exact ENNReal.ofReal_le_ofReal ha
  calc (E1 : ℝ≥0∞) * ENNReal.ofReal a1 ≤ ((Nn : ℝ≥0∞) * (E2 : ℝ≥0∞)) * (ENNReal.ofReal c * ENNReal.ofReal a2) :=
        mul_le_mul' h1 h2
    _ = _ := by ring

/-- Ladder weights are at least `1` and at most `(log L)²` once `e ≤ L`, `0 ≤ δ`, `0 ≤ P`. -/
theorem ladderWeight_ge_one (L γ δ P : ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 ≤ δ) (hP : 0 ≤ P) :
    1 ≤ Molecule.ladderWeight L γ δ P := by
  unfold Molecule.ladderWeight
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have h1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  refine le_min ?_ ?_
  · nlinarith
  · have : 0 ≤ δ * L ^ (2 * γ) * P := mul_nonneg (mul_nonneg hδ (Real.rpow_nonneg hL0.le _)) hP
    linarith

theorem ladderWeight_le (L γ δ P : ℝ) : Molecule.ladderWeight L γ δ P ≤ Real.log L ^ 2 :=
  min_le_left _ _

end WaveTurbulence.FinalCount
