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

/-- The normalized actual leading NT profile is the original integrated
J3 time coefficient times the actual singular spatial factor. Both active
energy and temporal Fourier integrals are exchanged from original joint L1. -/
theorem physical_approxApp_temporal_eq {d n : ℕ} {L δ γ : ℝ}
    (hL : 0 < L) (hδ : δ ≠ 0) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (hi : Integrable (Function.uncurry C))
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) W) t =
    (((δ/8)^n:ℝ):ℂ)*(∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))*singInt J W := by
  have he : (fun lam => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) W) =
      (fun lam => (((δ/8)^n:ℝ):ℂ)*(∫ β, C β lam)*singInt J W) := by
    funext lam
    exact physical_approxApp_frequency_eq hL hδ J C W lam
  rw [he,pairedInverseProfile]
  calc
    _ = ∫ lam, (((δ/8)^n:ℝ):ℂ)*((∫ β, C β lam)*e2 lam (t 0) (t 1))*singInt J W := by
      apply integral_congr_ae
      apply ae_of_all
      intro lam
      ring
    _ = (((δ/8)^n:ℝ):ℂ)*(∫ lam, (∫ β, C β lam)*e2 lam (t 0) (t 1))*singInt J W := by
      rw [integral_mul_const,integral_const_mul]
    _ = _ := by
      have ht := integral_integral_e2_eq_pairedProfile hi t
      change (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1)) =
        (∫ lam, (∫ β, C β lam)*e2 lam (t 0) (t 1)) at ht
      rw [← ht]

/-- The original SRep zeroth derivative mass supplies the joint L1
needed for the physical leading time identity; no integrability witness
is added to the source premises. -/
theorem physical_approxApp_temporal_eq_of_SRep {d n : ℕ} {L δ γ : ℝ}
    (hL : 0 < L) (hδ : δ ≠ 0) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    {θ a b A N : ℝ} (hθ : 0 ≤ θ) (hS : SRep θ a b A N C)
    (W : (Fin n → Mom d) → (Fin n → Mom d) → ℂ) (t : Fin 2 → ℝ) :
    pairedInverseProfile (fun lam => (((δ/(2*L^((d:ℝ)-γ)))^(2*n):ℝ):ℂ)*
      approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) W) t =
    (((δ/8)^n:ℝ):ℂ)*(∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))*singInt J W := by
  have hm : (∫⁻ β, ∫⁻ lam, wL θ lam*‖C β lam‖ₑ) ≤ ENNReal.ofReal N := by
    simpa only [dnorm_zero,gev,Nat.mul_zero,Nat.factorial_zero,pow_zero,Nat.cast_one,mul_one]
      using hS.norm 0
  exact physical_approxApp_temporal_eq hL hδ J C
    (integrable_symbol_of_weighted_mass hS.reg hθ hm) W t

end WaveTurbulence.RegAsymp
