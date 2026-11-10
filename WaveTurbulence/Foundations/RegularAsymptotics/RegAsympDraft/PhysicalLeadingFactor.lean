/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.HalfCellWickTemporal
public import WaveTurbulence.Foundations.RegAsymp.Normalization
public import WaveTurbulence.Foundations.RegAsymp.TimeCoefficientMass

/-! # Exact physical leading normalization and the original integrated time coefficient -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT ClassJR WithLp

/-- Original coupling with the physical NT parameter2delta gives delta/8
per link before the spatial singular integral contributes its factor2. -/
theorem physical_leading_normalization (n d : ℕ) {L δ γ : ℝ}
    (hL : 0 < L) (hδ : δ ≠ 0) :
    (δ/(2*L^((d:ℝ)-γ)))^(2*n)*(L^(2*(d:ℝ)-2*γ)*(2*δ)⁻¹)^n = (δ/8)^n := by
  rw [lattice_scale_square hL d γ]
  simpa only [one_mul,show (4:ℝ)*2 = 8 by norm_num] using
    scaled_normalization_identity (X := L^((d:ℝ)-γ)) n (ne_of_gt (Real.rpow_pos_of_pos hL _)) hδ
      (by norm_num : (2:ℝ) ≠ 0) 1

/-- Exact normalized leading frequency at every temporal frequency,
with the active Euclidean variables identified with the original coordinates. -/
theorem physical_approxApp_frequency_eq {d n : ℕ} {L δ γ : ℝ}
    (hL : 0 < L) (hδ : δ ≠ 0) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (lam : ℝ × ℝ) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) W =
    (((δ/8)^n:ℝ):ℂ)*(∫ β, C β lam)*singInt J W := by
  have hcoord (lam : ℝ × ℝ) :
      (∫ Ω : EuclideanSpace ℝ {j : Fin n // j ∉ J}, C (ofLp Ω) lam) = ∫ β, C β lam :=
    (PiLp.volume_preserving_ofLp _).integral_comp
      (MeasurableEquiv.toLp 2 (_ → ℝ)).symm.measurableEmbedding (fun β => C β lam)
  have hc : Complex.ofReal ((δ/(2*L^((d:ℝ)-γ)))^(2*n))*
      Complex.ofReal (L^(2*(d:ℝ)-2*γ)*(2*δ)⁻¹)^n = Complex.ofReal ((δ/8)^n) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_pow] using
      congrArg Complex.ofReal (physical_leading_normalization n d hL hδ)
  unfold approxApp
  rw [hcoord]
  calc
    _ = (Complex.ofReal ((δ/(2*L^((d:ℝ)-γ)))^(2*n))*
        Complex.ofReal (L^(2*(d:ℝ)-2*γ)*(2*δ)⁻¹)^n)*(∫ β, C β lam)*singInt J W := by ring
    _ = _ := by rw [hc]

end WaveTurbulence.RegAsymp
