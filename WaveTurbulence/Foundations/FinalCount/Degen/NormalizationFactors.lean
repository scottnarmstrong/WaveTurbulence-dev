/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Degen.CommonParameters
public import WaveTurbulence.Foundations.FinalCount.MoleculeRestrictedCount
public import WaveTurbulence.Foundations.FinalCount.Degen.LatticeLabels
import Mathlib.Tactic

/-! # Exact scalar normalization of the source countE inequalities

All actual maximal-ladder factors are retained in this module. Their
geometric comparison is a separate proof, not a hypothesis concealed here.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.Degen
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Multiplying the count inequality by the exact normalization gives the
exact normalized ratio, including all actual ladder factors. -/
theorem normalized_count_mono {A B : ℕ∞} {K : ℕ} {a b : ℝ}
    (hcount : A ≤ K * B) (ha : 0 ≤ a) (hb : 0 < b) :
    (A : ℝ≥0∞) * ENNReal.ofReal a ≤
      ENNReal.ofReal ((K : ℝ) * a / b) * ((B : ℝ≥0∞) * ENNReal.ofReal b) := by
  have hh := ENat.toENNReal_mono hcount
  rw [ENat.toENNReal_mul] at hh
  calc
    _ ≤ ((K : ℝ≥0∞) * (B : ℝ≥0∞)) * ENNReal.ofReal a := mul_le_mul_of_nonneg_right hh bot_le
    _ = ENNReal.ofReal ((K : ℝ) * a / b) * ((B : ℝ≥0∞) * ENNReal.ofReal b) := by
      have hscalar : ENNReal.ofReal ((K : ℝ) * a / b) * ENNReal.ofReal b =
          ENNReal.ofReal (K : ℝ) * ENNReal.ofReal a := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ) * a / b)]
        rw [show (K : ℝ) * a / b * b = (K : ℝ) * a by field_simp]
        exact ENNReal.ofReal_mul (Nat.cast_nonneg K)
      rw [show (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) by simp only [ENNReal.ofReal_natCast]]
      calc
        _ = (ENNReal.ofReal (K : ℝ) * ENNReal.ofReal a) * (B : ℝ≥0∞) := by ring
        _ = (ENNReal.ofReal ((K : ℝ) * a / b) * ENNReal.ofReal b) * (B : ℝ≥0∞) := by rw [hscalar]
        _ = _ := by ring

end WaveTurbulence.Degen
