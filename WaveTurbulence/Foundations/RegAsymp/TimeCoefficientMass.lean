/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnvelopeMass
public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction
import WaveTurbulence.Foundations.ClassJR.MCCase1

/-! # Dimension-independent time restriction bounds for integrated J3 coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WaveTurbulence.Fourier WithLp
open scoped ENNReal

/-- The source zeroth derivative mass gives absolute joint integrability. -/
theorem integrable_symbol_of_weighted_mass {ι : Type} [Fintype ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {θ N : ℝ} (hθ : 0 ≤ θ)
    (hmass : (∫⁻ β, ∫⁻ lam, wL θ lam*‖C β lam‖ₑ) ≤ ENNReal.ofReal N) :
    Integrable (Function.uncurry C) := by
  refine ⟨hC.meas.aestronglyMeasurable,hasFiniteIntegral_iff_enorm.mpr ?_⟩
  have he : (∫⁻ p : (ι → ℝ) × (ℝ × ℝ), ‖Function.uncurry C p‖ₑ) =
      ∫⁻ β, ∫⁻ lam, ‖C β lam‖ₑ :=
    lintegral_prod (μ := volume) (ν := volume) _ hC.meas.measurable.enorm.aemeasurable
  rw [he]
  apply lt_of_le_of_lt _ (hmass.trans_lt ENNReal.ofReal_lt_top)
  apply lintegral_mono
  intro β
  apply lintegral_mono
  intro lam
  exact le_mul_of_one_le_left bot_le (one_le_wL hθ lam)

/-- Absolute joint integrability identifies the integrated source time
coefficient with the original-frequency inverse profile. -/
theorem integral_integral_e2_eq_pairedProfile {ι : Type} [Fintype ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : Integrable (Function.uncurry C))
    (t : Fin 2 → ℝ) :
    (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1)) =
      pairedInverseProfile (fun lam => ∫ β, C β lam) t := by
  have hE : Continuous (fun p : (ι → ℝ) × (ℝ × ℝ) => e2 p.2 (t 0) (t 1)) := by
    unfold e2
    fun_prop
  have hCE := hC.mul_bdd (c := 1) hE.aestronglyMeasurable
    (ae_of_all _ (fun p => (norm_e2 p.2 (t 0) (t 1)).le))
  rw [integral_integral_swap hCE]
  simp only [pairedInverseProfile,integral_mul_const]

/-- Integrating all active energy variables retains a geometric source
mass; the estimate has no cardinality or derivative-order loss. -/
theorem mixedRestrictionNorm00_integrated_coefficient_le {ι : Type} [Fintype ι]
    {C : (ι → ℝ) → ℝ × ℝ → ℂ} (hC : SymReg C) {η θ N A : ℝ}
    (hη : 0 ≤ η) (hηθ : η ≤ θ) (hN : 0 ≤ N) (hA : 0 ≤ A)
    (hmain : ∀ k, ∫⁻ β, ∫⁻ lam, wL θ lam*dnorm k C β lam ≤ gev N A k)
    {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) :
    mixedRestrictionNorm00 η T (Set.univ : Set Unit)
      (fun t _ => ∫ β, ∫ lam, C β lam*e2 lam ((t : Fin 2 → ℝ) 0) ((t : Fin 2 → ℝ) 1)) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff*
        (ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  have hzero : (∫⁻ β, ∫⁻ lam, wL θ lam*‖C β lam‖ₑ) ≤ ENNReal.ofReal N := by
    simpa only [dnorm_zero,gev,Nat.mul_zero,Nat.factorial_zero,pow_zero,Nat.cast_one,mul_one]
      using hmain 0
  have hCi := integrable_symbol_of_weighted_mass hC (hη.trans hηθ) hzero
  have hbound (lam : ℝ × ℝ) : ‖∫ β, C β lam‖ₑ ≤ derivativeCoefficientEnvelope C lam := by
    apply (enorm_integral_le_lintegral_enorm _).trans
    simpa only [dnorm_zero,Nat.mul_zero,Nat.factorial_zero,Nat.cast_one,ENNReal.ofReal_one,one_mul]
      using derivativeCoefficientEnvelope_dominates C 0 lam
  have hmass := derivativeCoefficientEnvelope_mass_le hC hN hmain
  have hmassη : (∫⁻ lam, wL η lam*derivativeCoefficientEnvelope C lam) ≤
      ENNReal.ofReal N*∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial) := by
    apply le_trans (lintegral_mono (fun lam => mul_le_mul' (temporalWeight_mono hηθ lam) le_rfl)) hmass
  have hfin : (∫⁻ lam, wL η lam*derivativeCoefficientEnvelope C lam) < ⊤ :=
    hmassη.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (summable_gevrey_ratio A hA).tsum_ofReal_lt_top)
  have hMi : Integrable (fun lam => ∫ β, C β lam) :=
    integrable_of_wL_envelope hη hCi.integral_prod_right.aestronglyMeasurable
      (ae_of_all _ hbound) hfin
  simp_rw [integral_integral_e2_eq_pairedProfile hCi]
  exact (mixedRestrictionNorm00_pairedProfile_le hη hT Set.univ (fun _ => hMi)
    (measurable_derivativeCoefficientEnvelope hC) (fun _ => ae_of_all _ hbound)).trans
      (mul_le_mul' le_rfl hmassη)

end WaveTurbulence.RegAsymp
