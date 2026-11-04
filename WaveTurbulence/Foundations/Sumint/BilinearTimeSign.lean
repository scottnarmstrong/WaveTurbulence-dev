/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.MinorArcSums
public import WaveTurbulence.Foundations.WeylSums.HuaOrthogonality
import Mathlib.Tactic

/-!
# Reversing the bilinear time direction without a frequency cost

The pair time whose linear modulations are fixed is the outer source
time. Integrating the other time reverses the bilinear time direction.
Complex conjugation changes that direction while negating only the two
unrestricted spatial modulations.
-/

public section

open ComplexConjugate

namespace WaveTurbulence.Sumint

/-- Conjugation reverses the bilinear time and both linear frequencies. -/
theorem conj_bilinearLatticeSum_time_neg {d : ℕ} (L s : ℝ) (a b ξ ζ : Mom d) :
    conj (WeylSums.bilinearLatticeSum L (-s) a b ξ ζ) =
      WeylSums.bilinearLatticeSum L s a b (-ξ) (-ζ) := by
  unfold WeylSums.bilinearLatticeSum
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro q
  rw [map_mul,Complex.conj_ofReal,WeylSums.conj_e]
  apply congrArg (fun θ : ℝ =>
    ((WeylSums.latticeCutoff (latticePoint L q.1-a)*WeylSums.latticeCutoff (latticePoint L q.2-b) : ℝ) : ℂ) *
      WeylSums.e θ)
  simp only [inner_neg_right]
  ring

/-- Reversing the pair time has no effect on its norm after negating unrestricted modulations. -/
theorem norm_bilinearLatticeSum_time_neg {d : ℕ} (L s : ℝ) (a b ξ ζ : Mom d) :
    ‖WeylSums.bilinearLatticeSum L (-s) a b ξ ζ‖ =
      ‖WeylSums.bilinearLatticeSum L s a b (-ξ) (-ζ)‖ := by
  rw [← conj_bilinearLatticeSum_time_neg]
  exact (Complex.norm_conj _).symm

end WaveTurbulence.Sumint
