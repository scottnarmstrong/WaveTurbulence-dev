/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SNormOperations
public import WaveTurbulence.Foundations.Sumint.Words
/-! Assemble the exact spatial norm from weighted coordinate-word estimates, with ENNReal bounds. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open NormBridgeScratch
open scoped ENNReal

theorem SNorm_le_of_word_enorm_bounds {d A B : ℕ} (f : Mom d → ℂ)
    (hf : ContDiff ℝ A f) (C : ℝ≥0∞)
    (h : ∀ word : List (Fin d), word.length ≤ A → ∀ x,
      ‖((jbr x ^ B : ℝ) : ℂ) * wordD word f x‖ₑ ≤ C) : SNorm A B f ≤ C := by
  rw [SNorm_eq_spatialNorm]
  simp only [Fourier.spatialNorm, ite_eq_left (Or.inr hf)]
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  apply iSup_le
  intro ρ
  apply iSup_le
  intro x
  have hf' : ContDiff ℝ n f := hf.of_le (by exact_mod_cast hn)
  have hh := h (List.ofFn ρ) (by simpa using hn) x
  rw [← ofReal_norm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (jbr_pos x).le B)] at hh
  rw [← ofReal_jbr_mul_norm, momentumDerivative_eq_wordD ρ hf']
  exact hh

end WaveTurbulence.LGSpine
