/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.MixedNorm

/-! # Constant spatial functions in the actual zero-weight source norm -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp

/-- Constant functions have at most their constant norm in every unweighted derivative norm. -/
theorem tree_spatialNorm_const_le {d : ℕ} (N : ℕ) (c : ℂ) :
    Fourier.spatialNorm (d := d) N 0 (fun _ => c) ≤ ENNReal.ofReal ‖c‖ := by
  rw [Fourier.spatialNorm,ite_eq_left (Or.inr contDiff_const)]
  apply iSup_le
  intro n
  apply iSup_le
  intro _hn
  apply iSup_le
  intro ρ
  unfold Fourier.momentumSupNorm
  apply iSup_le
  intro k
  by_cases hn : n=0
  · subst n
    simp only [Fourier.momentumDerivative_zero,pow_zero,ENNReal.ofReal_one,one_mul]
    rw [← ofReal_norm]
  · simp [Fourier.momentumDerivative,iteratedFDeriv_const_of_ne hn]

end WaveTurbulence.RegAsymp
