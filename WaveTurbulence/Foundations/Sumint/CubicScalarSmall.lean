/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CubicScalarAmplitude
import Mathlib.Tactic

/-!
# The cubic small-time lattice estimate in one spatial coordinate

Poisson summation followed by the landed absolutely convergent cubic
frequency bound gives `C L^3/(1+|s|+|t|)`, uniformly in the translated
cutoff centers and all linear modulations.
-/

public section

namespace WaveTurbulence.Sumint

/-- Reflection aligns the dual Fourier frequencies with the landed positive cubic convention. -/
theorem cubic_scalar_dual_sum_eq (kind : LemLin.CubicPhase)
    (f : Fin 3 → LemLin.ScalarCutoff) (L s t : ℝ) (a ν : Fin 3 → ℝ) :
    (∑' m : Fin 3 → ℤ, ‖Fourier.timeFourier
      (translatedCubicAmplitude kind f s t a ν) (fun j => L * (m j : ℝ))‖) =
    ∑' m : Fin 3 → ℤ, ‖LemLin.scalarCubicIntegral kind f s t
      (LemLin.scalarLatticeFrequency L (ν + LemLin.cubicFrequencyShift kind s t a) m)‖ := by
  rw [← (Equiv.neg (Fin 3 → ℤ)).tsum_eq]
  apply tsum_congr
  intro m
  rw [timeFourier_translatedCubicAmplitude, LemLin.norm_translatedScalarCubicIntegral]
  congr 2
  funext j
  simp [LemLin.scalarLatticeFrequency]
  <;> ring

/-- Uniform absolute Poisson bound for the actual scalar cubic lattice series. -/
theorem exists_scalar_cubic_small_bound (f : Fin 3 → LemLin.ScalarCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L → ∀ (kind : LemLin.CubicPhase) (s t : ℝ),
      |s| ≤ L → |t| ≤ L → ∀ a ν : Fin 3 → ℝ,
      ‖∑' m : Fin 3 → ℤ, translatedCubicAmplitude kind f s t a ν
        (fun j => (m j : ℝ) / L)‖ ≤ C * L^3 / LemLin.cubicScale s t := by
  obtain ⟨C, hC, hb⟩ := LemLin.scalarCubic_lattice_sum f
  refine ⟨C, hC, ?_⟩
  intro L hL kind s t hs ht a ν
  have hLp : 0 < L := by linarith
  have hP := norm_lattice_sum_le_poisson_smooth_compact
    (translatedCubicAmplitude_contDiff kind f s t a ν)
    (translatedCubicAmplitude_hasCompactSupport kind f s t a ν) hLp
  rw [cubic_scalar_dual_sum_eq] at hP
  exact hP.trans ((mul_le_mul_of_nonneg_left
    (hb hL kind s t hs ht (ν + LemLin.cubicFrequencyShift kind s t a)).2
    (pow_nonneg hLp.le _)).trans_eq (by ring))

end WaveTurbulence.Sumint
