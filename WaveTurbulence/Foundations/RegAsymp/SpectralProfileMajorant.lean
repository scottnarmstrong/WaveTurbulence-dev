/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfileRestriction

/-! # Integrating a common source profile bound against the spatial spectrum

The auxiliary measure may include counting measure on leaf centers and
Lebesgue measure on their independent frequencies. The vector supremum
continues to lie inside the time-frequency integral.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR WaveTurbulence.Fourier
open scoped ENNReal

/-- Integration of the spatial first-moment envelope costs its mass once. -/
theorem enorm_spectral_integral_le {Ω V : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H : Ω → V → ℂ} {p : Ω → ℝ≥0∞} (hp : Measurable p)
    {B : ℝ≥0∞} (hbound : ∀ q, ∀ᵐ ω ∂μ, ‖H ω q‖ₑ ≤ p ω*B) (q : V) :
    ‖∫ ω, H ω q ∂μ‖ₑ ≤ (∫⁻ ω, p ω ∂μ)*B := by
  apply (enorm_integral_le_lintegral_enorm _).trans
  exact (lintegral_mono_ae (hbound q)).trans_eq (lintegral_mul_const _ hp)

/-- A common local λ envelope and the spatial first moment control the
restriction norm of the fully integrated profile. This includes arbitrary
vector parameters inside the Fourier supremum. -/
theorem mixedRestrictionNorm00_spectral_profile_le {Ω V : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {η : ℝ} (hη : 0 ≤ η)
    {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1)
    (K : Set V) {H : (ℝ × ℝ) → Ω → V → ℂ}
    (hH : ∀ q, AEStronglyMeasurable (fun lam => ∫ ω, H lam ω q ∂μ))
    {p : Ω → ℝ≥0∞} (hp : Measurable p) (hpfinite : (∫⁻ ω, p ω ∂μ) < ⊤)
    {B : (ℝ × ℝ) → ℝ≥0∞} (hB : Measurable B)
    (hBfinite : (∫⁻ lam, wL η lam*B lam) < ⊤)
    (hbound : ∀ q, ∀ᵐ lam : ℝ × ℝ, ∀ᵐ ω ∂μ, ‖H lam ω q‖ₑ ≤ p ω*B lam) :
    mixedRestrictionNorm00 η T K
      (fun t q => pairedInverseProfile (fun lam => ∫ ω, H lam ω q ∂μ) t) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff *
        ((∫⁻ ω, p ω ∂μ)*(∫⁻ lam, wL η lam*B lam)) := by
  let M := ∫⁻ ω, p ω ∂μ
  let E := fun lam => M*B lam
  have hmE : Measurable E := measurable_const.mul hB
  have hb (q : V) : ∀ᵐ lam : ℝ × ℝ, ‖∫ ω, H lam ω q ∂μ‖ₑ ≤ E lam := by
    filter_upwards [hbound q] with lam hlam
    exact enorm_spectral_integral_le hp (fun _ : Unit => hlam) ()
  have hmass : (∫⁻ lam, wL η lam*E lam) = M*(∫⁻ lam, wL η lam*B lam) := by
    calc
      _ = ∫⁻ lam, M*(wL η lam*B lam) := by
        apply lintegral_congr
        intro lam
        dsimp only [E]
        ac_rfl
      _ = _ := lintegral_const_mul (f := fun lam => wL η lam*B lam) _ ((measurable_wL η).mul hB)
  have hfE : (∫⁻ lam, wL η lam*E lam) < ⊤ := by
    rw [hmass]
    exact ENNReal.mul_lt_top hpfinite hBfinite
  have hi (q : V) : Integrable (fun lam => ∫ ω, H lam ω q ∂μ) :=
    integrable_of_wL_envelope hη (hH q) (hb q) hfE
  exact (mixedRestrictionNorm00_pairedProfile_le hη hT K hi hmE hb).trans_eq
    (congrArg (fun m => ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff*m) hmass)

end WaveTurbulence.RegAsymp
