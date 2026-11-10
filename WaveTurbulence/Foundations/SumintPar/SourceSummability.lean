/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormPartitionIdentity
public import WaveTurbulence.Foundations.SumintPar.LocalizedLatticeMass

/-!
# Genuine absolute convergence of the original source lattice sum

The nonnegative cell partition, summed Fourier coefficient mass and fixed
cutoff support count prove absolute convergence before any oscillatory
estimate. The source time integrals have a common absolute bound because
the modulus of the phase is independent of the lattice and output momentum.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- A common finite absolute phase-integral bound, independent of every lattice input. -/
theorem norm_source_phaseIntegral_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t t' t'' : ℝ) :
    ‖∫ τ in D.timeDom hI t t' t'', D.phase L γ δ η x r t τ‖ ≤
      ∫ τ in D.timeDom hI t t' t'', ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  simp_rw [norm_phase]

end WaveTurbulence.SumintPar
