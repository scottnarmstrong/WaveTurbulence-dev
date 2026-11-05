/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GateTypes
public import WaveTurbulence.Foundations.Gaussian.ComplexGaussian
public import Mathlib.Probability.Independence.InfinitePi
/-! Joint Gaussian data-law invariance under deterministic coefficientwise unit phases. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory

/-- The literal IsGaussianData predicates determine the entire array law. -/
theorem gaussian_joint_law {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) :
    μ.map (fun ω n => g n ω) = Measure.infinitePi (fun _ : Fin d → ℤ => stdComplexGaussian) := by
  rw [iIndepFun.map_fun_eq_infinitePi_map hG.1 hG.2.1]
  congr 1
  funext n
  exact hG.2.2 n

/-- Independent complex Gaussians remain such after arbitrary fixed unit phases. -/
theorem isGaussianData_mul_phase {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) (phase : (Fin d → ℤ) → ℂ) (hp : ∀ n, ‖phase n‖ = 1) :
    IsGaussianData μ (fun n ω => phase n * g n ω) := by
  refine ⟨fun n => (hG.1 n).const_mul _, ?_, fun n => ?_⟩
  · exact hG.2.1.comp (fun n z => phase n * z) (fun _ => by fun_prop)
  · change μ.map ((fun z => phase n * z) ∘ g n) = stdComplexGaussian
    rw [← Measure.map_map (by fun_prop) (hG.1 n), hG.2.2 n, map_mul_stdComplexGaussian _ (hp n)]

/-- Gauge and spatial modulation preserve the joint law of the actual initial coefficients. -/
theorem initialCoeff_map_mul_phase {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {g : (Fin d → ℤ) → Ω → ℂ}
    (hG : IsGaussianData μ g) (L : ℝ) (φ : Mom d → ℝ)
    (phase : (Fin d → ℤ) → ℂ) (hp : ∀ n, ‖phase n‖ = 1) :
    μ.map (fun ω n => phase n * initialCoeff L φ g ω n) = μ.map (initialCoeff L φ g) := by
  let scale : ((Fin d → ℤ) → ℂ) → (Fin d → ℤ) → ℂ :=
    fun c n => (Real.sqrt (φ (latticePoint L n)) : ℂ) * c n
  have hs : Measurable scale := measurable_pi_iff.mpr (fun n => (measurable_pi_apply n).const_mul _)
  have h1 : (fun ω n => phase n * initialCoeff L φ g ω n) =
      scale ∘ (fun ω n => phase n * g n ω) := by
    funext ω n
    dsimp only [scale, Function.comp_apply, initialCoeff]
    ring
  have h2 : initialCoeff L φ g = scale ∘ (fun ω n => g n ω) := rfl
  rw [h1, h2, ← Measure.map_map hs (measurable_pi_iff.mpr (fun n => (hG.1 n).const_mul _)),
    ← Measure.map_map hs (measurable_pi_iff.mpr hG.1),
    gaussian_joint_law (isGaussianData_mul_phase hG phase hp), gaussian_joint_law hG]

end WaveTurbulence.Induct
