/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CellMultiplierMass
public import WaveTurbulence.Foundations.Fourier.Norm00VCutoff
public import WaveTurbulence.Foundations.Sumint.TimeBridge

/-!
# A finite explicit step-dependent multiplier constant for each time cell

The constant is independent of the cell center, scale h and source
input count. Every multiplier regularity of absolute value at most one
costs only this constant times h inverse.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The actual fixed cell scalar-mass constant is finite. -/
theorem cellMultiplierMassConstant_lt_top (N : ℕ) : cellMultiplierMassConstant N < ⊤ := by
  have ht : scalarFourierMass timePartitionScalar < ⊤ :=
    scalarFourierMass_lt_top_of_smooth_compact hasCompactSupport_timePartitionScalar contDiff_timePartitionScalar
  have hp : (∏ k : Fin 3, scalarFourierMass (timeInverseExpScalar N (if k = 0 then 1 else -1))) < ⊤ :=
    ENNReal.prod_lt_top (fun k _ => scalarFourierMass_lt_top_of_smooth_compact
      (hasCompactSupport_timeInverseExpScalar N _) (contDiff_timeInverseExpScalar N _))
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ht) hp

/-- An explicit real majorant, depending only on the source step range, for the compact cell multiplier cost. -/
@[expose] noncomputable def cellMultiplierRealConstant (N : ℕ) : ℝ :=
  max 1 (2*cellMultiplierMassConstant N).toReal

/-- The real cell multiplier constant is at least one. -/
theorem one_le_cellMultiplierRealConstant (N : ℕ) : 1 ≤ cellMultiplierRealConstant N := le_max_left _ _

/-- The exact cell multiplier cost has its explicit real h-inverse bound. -/
theorem cutoffMultiplierConstant_cell_le_real (N : ℕ) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : |θ| ≤ 1) (j : ℤ) :
    Fourier.cutoffMultiplierConstant θ (cellInverseExponential N h j) ≤
      ENNReal.ofReal (cellMultiplierRealConstant N*h⁻¹) := by
  apply (cutoffMultiplierConstant_cell_le N hh hθ j).trans
  have hfinite : 2*cellMultiplierMassConstant N < ⊤ := ENNReal.mul_lt_top (by norm_num) (cellMultiplierMassConstant_lt_top N)
  have hc : 2*cellMultiplierMassConstant N ≤ ENNReal.ofReal (cellMultiplierRealConstant N) := by
    rw [← ENNReal.ofReal_toReal hfinite.ne]
    exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  rw [ENNReal.ofReal_mul (zero_le_one.trans (one_le_cellMultiplierRealConstant N))]
  exact mul_le_mul' hc le_rfl

/-- Multiplication by the actual compact cell cutoff preserves the drafted norm with the explicit h-inverse cost. -/
theorem XNorm00_mul_cellInverseExponential_le {V : Type*} (N : ℕ) {h θ : ℝ}
    (hh : h ∈ Ioc (0:ℝ) 1) (hθ : |θ| ≤ 1) (j : ℤ)
    (F : (Fin 3 → ℝ) → V → ℂ) (hF : XNorm00 θ F < ⊤) :
    XNorm00 θ (fun z v => F z v*cellInverseExponential N h j z) ≤
      ENNReal.ofReal (cellMultiplierRealConstant N*h⁻¹)*XNorm00 θ F := by
  simp_rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00] at hF ⊢
  exact (Fourier.mixedFourierNorm00_mul_cutoff_le θ hF
    (hasCompactSupport_cellInverseExponential N h j) (contDiff_cellInverseExponential N h j)).trans
      (mul_le_mul' (cutoffMultiplierConstant_cell_le_real N hh hθ j) le_rfl)

end WaveTurbulence.Sumint
