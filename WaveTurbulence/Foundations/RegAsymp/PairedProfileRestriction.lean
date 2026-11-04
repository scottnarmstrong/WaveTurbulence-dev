/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.PairedProfileMajorant
public import WaveTurbulence.Foundations.RegAsymp.UnitSquareCutoff

/-! # Restriction to the source time square

A fixed compact extension turns the source inverse profile estimate into
an estimate for the restriction norm, with the vector supremum inside
the frequency integral.
-/

public section
namespace WaveTurbulence.RegAsymp
open MeasureTheory WaveTurbulence.Fourier ClassJR
open scoped ENNReal

/-- The source time square may be restricted further without changing the constant. -/
theorem mixedRestrictionNorm00_pairedProfile_le {V : Type*} {η : ℝ} (hη : 0 ≤ η)
    {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1)
    (K : Set V) {A : (ℝ × ℝ) → V → ℂ}
    (hA : ∀ q, Integrable (fun lam => A lam q))
    {B : (ℝ × ℝ) → ℝ≥0∞} (hB : Measurable B)
    (hbound : ∀ q, ∀ᵐ lam : ℝ × ℝ, ‖A lam q‖ₑ ≤ B lam) :
    mixedRestrictionNorm00 η T K
      (fun t q => pairedInverseProfile (fun lam => A lam q) t) ≤
      ENNReal.ofReal (2^η)*timeFourierNorm η unitSquareCutoff*
        (∫⁻ lam, wL η lam*B lam) := by
  let G := fun t q => unitSquareCutoff t*pairedInverseProfile (fun lam => A lam q) t
  have hG : ∀ (t : T) (q : K), G t q = pairedInverseProfile (fun lam => A lam q) t := by
    intro t q
    dsimp only [G]
    rw [unitSquareCutoff_eq_one (hT t t.property), one_mul]
  calc
    _ ≤ mixedFourierNorm00 η G := by
      unfold mixedRestrictionNorm00
      exact iInf_le_of_le G (iInf_le_of_le hG le_rfl)
    _ ≤ _ := mixedFourierNorm00_pairedProfile_le hη integrable_unitSquareCutoff hA hB hbound

/-- A finite weighted common envelope supplies the integrability needed by
Fourier inversion. The exponent is nonnegative, so the weight dominates one. -/
theorem integrable_of_wL_envelope {η : ℝ} (hη : 0 ≤ η)
    {A : (ℝ × ℝ) → ℂ} (hA : AEStronglyMeasurable A)
    {B : (ℝ × ℝ) → ℝ≥0∞} (hbound : ∀ᵐ lam : ℝ × ℝ, ‖A lam‖ₑ ≤ B lam)
    (hfinite : (∫⁻ lam, wL η lam*B lam) < ⊤) : Integrable A := by
  refine ⟨hA, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  apply lt_of_le_of_lt (lintegral_mono_ae hbound)
  exact lt_of_le_of_lt (lintegral_mono fun lam =>
    le_mul_of_one_le_left bot_le (one_le_wL hη lam)) hfinite

end WaveTurbulence.RegAsymp
