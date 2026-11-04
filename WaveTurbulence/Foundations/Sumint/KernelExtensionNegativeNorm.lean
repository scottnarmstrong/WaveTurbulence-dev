/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.KernelExtension
public import WaveTurbulence.Foundations.Sumint.NegativeEndpointKernel
public import WaveTurbulence.Foundations.Sumint.FourierNormMajorant

/-!
# Negative Fourier norm of the rectangular extension operator

This is an auxiliary operator estimate for an arbitrary coefficient
family. A separate oscillatory argument must establish its input-mass
bound when the coefficient is a lattice sum. No source closure is
asserted by this conditional helper.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- A uniform input `L¹` bound gives a general-output negative Fourier norm
bound without paying the cardinality of the output carrier. -/
theorem kernelExtension_negative_norm_le {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (c h : ℝ) {V : Type*} (F : (D.S.TVar → ℝ) → V → ℂ)
    (hFm : ∀ v, Measurable (fun u => F u v))
    (hFi : ∀ v, IntegrableOn (fun u => F u v) (localInputTimeDomain D c h))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ v, (∫ u in localInputTimeDomain D c h, ‖F u v‖) ≤ B)
    {ε : ℝ} (hε : 0 < ε) :
    XNorm00 (-ε) (fun z v => kernelExtension D hI c h (fun u => F u v) z) ≤
      ENNReal.ofReal ((2*B) * ∫ ξ : Fin 3 → ℝ,
        Fourier.timeBracket ξ^(-ε) * ∏ j, 1/scalarBracket (ξ j)) := by
  let k := fun ξ : Fin 3 → ℝ => Fourier.timeBracket ξ^(-ε) *
    ∏ j, 1/scalarBracket (ξ j)
  have hpn (ξ : Fin 3 → ℝ) : 0 ≤ ∏ j, 1/scalarBracket (ξ j) :=
    Finset.prod_nonneg (fun j _ => div_nonneg (by norm_num)
      (zero_le_one.trans (one_le_scalarBracket _)))
  have hkn (ξ : Fin 3 → ℝ) : 0 ≤ k ξ := mul_nonneg
    (Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le _) (hpn ξ)
  rw [NormBridgeScratch.XNorm00_eq_mixedFourierNorm00]
  have hh := mixedFourierNorm00_le_integral_majorant (-ε)
    (fun z v => kernelExtension D hI c h (fun u => F u v) z)
    (fun v => integrable_kernelExtension D hI c h _ (hFm v) (hFi v))
    (fun ξ => (2*B)*k ξ) ((integrable_negative_endpoint_kernel hε).const_mul (2*B))
    (fun ξ => mul_nonneg (mul_nonneg (by norm_num) hB) (hkn ξ))
    (by
      intro ξ v
      have hb := (norm_timeFourier_kernelExtension_le D hI c h (fun u => F u v)
        (hFm v) (hFi v) ξ).trans
          (mul_le_mul_of_nonneg_right (hbound v) (mul_nonneg (by norm_num) (hpn ξ)))
      have ht := mul_le_mul_of_nonneg_left hb
        (Real.rpow_nonneg (Fourier.timeBracket_pos ξ).le (-ε))
      dsimp only [k]
      convert ht using 1; ring)
  simpa only [integral_const_mul] using hh

end WaveTurbulence.Sumint
