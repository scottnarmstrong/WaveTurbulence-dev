/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.FSCoeff
public import WaveTurbulence.Foundations.SumintSigned.NormModulation
public import WaveTurbulence.Foundations.SumintSigned.VectorExtension
public import WaveTurbulence.Foundations.SumintSigned.CountableExtensionMinkowski
public import WaveTurbulence.Foundations.SumintSigned.NormScalar
public import WaveTurbulence.Foundations.Layered.RestrictionCalculus
public import WaveTurbulence.Foundations.Fourier.CutoffMultiplication

/-! # Auxiliary facts for the countable Minkowski inequality of restriction norms -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS3.Mink
open WaveTurbulence WaveTurbulence.Fourier MeasureTheory Set
open scoped ENNReal

variable {r : ℕ} {V W : Type*}

/-- `XNorm00` only sees the a.e. class of each time slice. -/
theorem XNorm00_congr_ae (θ : ℝ) {G H : (Fin r → ℝ) → V → ℂ} (h : ∀ v, ∀ᵐ t, G t v = H t v) :
    XNorm00 θ G = XNorm00 θ H := by
  unfold XNorm00
  have hi : (∀ v, Integrable fun t => G t v) ↔ ∀ v, Integrable fun t => H t v :=
    forall_congr' fun v => integrable_congr (h v)
  by_cases hG : ∀ v, Integrable fun t => G t v
  · rw [ite_eq_left hG, ite_eq_left (hi.1 hG)]
    refine lintegral_congr fun lam => ?_
    congr 1
    refine iSup_congr fun v => ?_
    have : timeFT G lam v = timeFT H lam v := by
      unfold timeFT
      exact integral_congr_ae ((h v).mono fun t ht => by simp only [ht])
    rw [this]
  · rw [ite_eq_right hG, ite_eq_right (fun h' => hG (hi.2 h'))]

/-- Restricting the vector parameter does not increase `XNorm00`. -/
theorem XNorm00_comp_le (θ : ℝ) (G : (Fin r → ℝ) → V → ℂ) (φ : W → V) :
    XNorm00 θ (fun t w => G t (φ w)) ≤ XNorm00 θ G := by
  unfold XNorm00
  by_cases hG : ∀ v, Integrable fun t => G t v
  · rw [ite_eq_left hG, ite_eq_left (fun w => hG (φ w))]
    refine lintegral_mono fun lam => ?_
    refine mul_le_mul_right (iSup_le fun w => ?_) _
    exact le_iSup (fun v => ‖timeFT G lam v‖ₑ) (φ w)
  · rw [ite_eq_right hG]; exact le_top


/-- The representative is bounded by the Fourier norm (for `θ ≥ 0`). -/
theorem enorm_rep_le {θ : ℝ} (hθ : 0 ≤ θ) {f : (Fin r → ℝ) → ℂ} (hf : timeFourierNorm θ f < ⊤)
    (t : Fin r → ℝ) : ‖Regref.rep f t‖ₑ ≤ timeFourierNorm θ f := by
  have hi := integrable_of_timeFourierNorm_lt_top hf
  rw [timeFourierNorm_eq_lintegral hi]
  unfold Regref.rep
  refine le_trans ?_ (lintegral_mono fun ξ => ?_ : ∫⁻ ξ, ‖timeFourier f ξ‖ₑ ≤
    ∫⁻ ξ, timeWeight θ ξ * ‖timeFourier f ξ‖ₑ)
  · unfold timeFourier VectorFourier.fourierIntegral
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun ξ => ?_))
    simp [Circle.smul_def, enorm_mul]
  · refine le_mul_of_one_le_left bot_le ?_
    unfold timeWeight
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow (one_le_timeBracket ξ) hθ)

end WaveTurbulence.VineEstS3.Mink
