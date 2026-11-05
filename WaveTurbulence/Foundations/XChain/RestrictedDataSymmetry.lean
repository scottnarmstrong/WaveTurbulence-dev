/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GaussianDataSymmetry
/-! Initial-data law invariance persists under the unnormalized symmetric-event restriction. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

/-- A pointwise phase action preserves the preimage of a set invariant in both directions. -/
theorem phase_preimage_eq {ι Ω : Type*} (C : Ω → ι → ℂ) (phase : ι → ℂ)
    (hp : ∀ i, phase i ≠ 0) (A : Set (ι → ℂ))
    (hInv : ∀ c ∈ A, (fun i => phase i * c i) ∈ A)
    (hInv' : ∀ c ∈ A, (fun i => (phase i)⁻¹ * c i) ∈ A) :
    (fun ω i => phase i * C ω i) ⁻¹' A = C ⁻¹' A := by
  ext ω
  constructor
  · intro h
    have hi := hInv' _ h
    have he : (fun i => (phase i)⁻¹ * (phase i * C ω i)) = C ω := by
      funext i
      exact inv_mul_cancel_left₀ (hp i) _
    change C ω ∈ A
    rw [← he]
    exact hi
  · exact hInv _

/-- The exact conditional law needed for gauge and space-translation support. -/
theorem restricted_initialCoeff_map_phase {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) (L : ℝ) (φ : Mom d → ℝ)
    (phase : (Fin d → ℤ) → ℂ) (hp : ∀ n, ‖phase n‖ = 1)
    (A : Set ((Fin d → ℤ) → ℂ)) (hA : MeasurableSet A)
    (hInv : ∀ c ∈ A, (fun n => phase n * c n) ∈ A)
    (hInv' : ∀ c ∈ A, (fun n => (phase n)⁻¹ * c n) ∈ A) :
    (μ.restrict (initialCoeff L φ g ⁻¹' A)).map
      (fun ω n => phase n * initialCoeff L φ g ω n) =
      (μ.restrict (initialCoeff L φ g ⁻¹' A)).map (initialCoeff L φ g) := by
  have hC : Measurable (initialCoeff L φ g) :=
    measurable_pi_iff.mpr (fun n => (hG.1 n).const_mul _)
  have hCp : Measurable (fun ω n => phase n * initialCoeff L φ g ω n) :=
    measurable_pi_iff.mpr (fun n => ((measurable_pi_apply n).comp hC).const_mul _)
  have hp0 (n : Fin d → ℤ) : phase n ≠ 0 := by
    intro hn
    have h := hp n
    rw [hn, norm_zero] at h
    exact zero_ne_one h
  have hpre := phase_preimage_eq (initialCoeff L φ g) phase hp0 A hInv hInv'
  calc
    _ = (μ.restrict ((fun ω n => phase n * initialCoeff L φ g ω n) ⁻¹' A)).map
        (fun ω n => phase n * initialCoeff L φ g ω n) := by rw [hpre]
    _ = (μ.map (fun ω n => phase n * initialCoeff L φ g ω n)).restrict A :=
      (Measure.restrict_map hCp hA).symm
    _ = (μ.map (initialCoeff L φ g)).restrict A := by rw [initialCoeff_map_mul_phase hG L φ phase hp]
    _ = _ := Measure.restrict_map hC hA

/-- In particular, the gauge action preserves the initial-data law conditional on any event
satisfying the literal snapshot IsSymmetricEvent definition. -/
theorem restricted_initialCoeff_map_gauge {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) (L : ℝ) (φ : Mom d → ℝ) {F : Set Ω}
    (hF : IsSymmetricEvent L φ g F) (θ : ℝ) :
    (μ.restrict F).map (fun ω n => Complex.exp ((θ : ℂ) * Complex.I) * initialCoeff L φ g ω n) =
      (μ.restrict F).map (initialCoeff L φ g) := by
  obtain ⟨A, hA, rfl, hgauge, _⟩ := hF
  apply restricted_initialCoeff_map_phase hG L φ _
    (fun _ => Complex.norm_exp_ofReal_mul_I θ) A hA (hgauge θ)
  intro c hc
  have he : (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  simpa only [he] using hgauge (-θ) c hc

end WaveTurbulence.Induct
