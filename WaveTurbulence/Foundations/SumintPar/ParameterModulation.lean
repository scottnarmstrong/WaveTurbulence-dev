/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.NormModulation
public import WaveTurbulence.Foundations.SumintPar.ParameterBound
import Mathlib.Tactic

/-!
# The source summed modulation and the exact parameter maximum

The source uses a π phase, while the Fourier character uses 2π. Its
frequency is therefore one half of the parameter sum in the first
coordinate and zero in the other two coordinates.
-/

@[expose] public section
set_option autoImplicit false

open scoped ENNReal

namespace WaveTurbulence.SumintPar

/-- The exact coordinate frequency of the source output modulation. -/
@[expose] noncomputable def sourceModulationFrequency (θ : ℝ) : Fin 3 → ℝ := ![θ/2,0,0]

/-- The π source phase is exactly the canonical Fourier character at the half frequency. -/
theorem sourceModulationFrequency_char (θ : ℝ) (z : Fin 3 → ℝ) :
    (Real.fourierChar (Fourier.timePairing 3 z (sourceModulationFrequency θ)) : ℂ) =
      Complex.exp ((Real.pi * θ * z 0 : ℝ) * Complex.I) := by
  change (Real.fourierChar (∑ j, z j * sourceModulationFrequency θ j) : ℂ) = _
  simp only [sourceModulationFrequency, Fin.sum_univ_succ, Matrix.cons_val_zero,
    add_zero, Fin.sum_univ_zero]
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The half-frequency bracket is at most the scalar bracket of the full summed parameter. -/
theorem timeBracket_sourceModulationFrequency_le (θ : ℝ) :
    Fourier.timeBracket (sourceModulationFrequency θ) ≤ scalarBracket θ := by
  apply Fourier.timeBracket_le (one_le_scalarBracket θ)
  intro j
  fin_cases j
  · change Real.sqrt (1+(θ/2)^2) ≤ Real.sqrt (1+θ^2)
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg θ]
  · simpa [sourceModulationFrequency] using one_le_scalarBracket θ
  · simpa [sourceModulationFrequency] using one_le_scalarBracket θ

/-- The exact source parameter maximum controls the summed modulation cost at every real regularity. -/
theorem XNorm00_source_modulate_le {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    {V : Type*} (s : ℝ) (F : (Fin 3 → ℝ) → V → ℂ) :
    XNorm00 s (fun z v => Complex.exp ((Real.pi * (∑ w, D.param w) * z 0 : ℝ) * Complex.I) * F z v) ≤
      ENNReal.ofReal (2^|s|) *
        ENNReal.ofReal ((((D.S.M : ℝ)+1) * parameterMaximum D)^|s|) * XNorm00 s F := by
  let θ := ∑ w, D.param w
  have he : (fun z v => Complex.exp ((Real.pi * (∑ w, D.param w) * z 0 : ℝ) * Complex.I) * F z v) =
      fun z v => Real.fourierChar (Fourier.timePairing 3 z (sourceModulationFrequency θ)) • F z v := by
    funext z v
    rw [Circle.smul_def, sourceModulationFrequency_char]
    rfl
  rw [he]
  have hb : Fourier.timeBracket (sourceModulationFrequency θ) ≤
      ((D.S.M : ℝ)+1) * parameterMaximum D :=
    (timeBracket_sourceModulationFrequency_le θ).trans (scalarBracket_sum_parameters_le D hI)
  have hw : Fourier.timeWeight |s| (sourceModulationFrequency θ) ≤
      ENNReal.ofReal ((((D.S.M : ℝ)+1) * parameterMaximum D)^|s|) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (Fourier.timeBracket_pos _).le hb (abs_nonneg _))
  exact (XNorm00_modulate_le_abs s F (sourceModulationFrequency θ)).trans
    (mul_le_mul' (mul_le_mul' le_rfl hw) le_rfl)

end WaveTurbulence.SumintPar
