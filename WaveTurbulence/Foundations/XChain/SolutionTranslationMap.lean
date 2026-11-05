/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TranslationPhase
public import WaveTurbulence.Foundations.XChain.CanonicalCoefficient
public import WaveTurbulence.Foundations.XChain.SolutionPhase
public import WaveTurbulence.Foundations.XChain.BaseEvent
/-! Translation invariance of the joint solution law under the literal symmetric-event restriction. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

theorem solution_joint_map_translation {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {L γ δ T : ℝ} (hL : 0 < L)
    (φ : Mom d → ℝ) {g : (Fin d → ℤ) → Ω → ℂ} (hG : IsGaussianData μ g)
    (F : Set Ω) (hFm : MeasurableSet F) (hF : IsSymmetricEvent L φ g F)
    (a : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (ha : ∀ ω ∈ F, IsASolution L γ δ T (initialCoeff L φ g ω) (a ω))
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (t : ι → Icc (0 : ℝ) T) (n : ι → (Fin d → ℤ)) (x : Mom d) :
    (μ.restrict F).map (fun ω j => a ω (t j) (n j)) =
      (μ.restrict F).map (fun ω j => translationPhase L x (n j) * a ω (t j) (n j)) := by
  let C := initialCoeff L φ g
  let Cp := fun ω n => translationPhase L x n * C ω n
  let Ψ := fun c j => canonicalCoeff L γ δ T (t j) (n j) c
  have hC : Measurable C := NLS.measurable_initialCoeff L φ hG.1
  have hCp : Measurable Cp := measurable_pi_iff.mpr
    (fun n => ((measurable_pi_apply n).comp hC).const_mul _)
  have hΨ : Measurable Ψ := measurable_pi_iff.mpr
    (fun j => measurable_canonicalCoeff L γ δ T (t j).2 (n j))
  have he0 : (fun ω j => a ω (t j) (n j)) =ᵐ[μ.restrict F] Ψ ∘ C := by
    apply ae_restrict_of_forall_mem hFm
    intro ω hω
    funext j
    exact (canonicalCoeff_eq hL (hrapid ω hω) (ha ω hω) (t j).2 (n j)).symm
  have heθ : Ψ ∘ Cp =ᵐ[μ.restrict F]
      (fun ω j => translationPhase L x (n j) * a ω (t j) (n j)) := by
    apply ae_restrict_of_forall_mem hFm
    intro ω hω
    have hc := rapidDecay_mul_phase (hrapid ω hω) (norm_translationPhase L x)
    have hs := isASolution_mul_phase (ha ω hω) (translationPhase L x)
      (norm_translationPhase L x) (translation_phase_relation L x)
    funext j
    exact canonicalCoeff_eq hL hc hs (t j).2 (n j)
  calc
    _ = (μ.restrict F).map (Ψ ∘ C) := Measure.map_congr he0
    _ = ((μ.restrict F).map C).map Ψ := (Measure.map_map hΨ hC).symm
    _ = ((μ.restrict F).map Cp).map Ψ := by rw [restricted_initialCoeff_map_translation hG L φ hF x]
    _ = (μ.restrict F).map (Ψ ∘ Cp) := Measure.map_map hΨ hCp
    _ = _ := Measure.map_congr heθ

end WaveTurbulence.Induct
