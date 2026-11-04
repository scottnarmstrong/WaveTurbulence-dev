/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.CompactFourier
public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition

/-! # Translation-uniform Fourier weights for shifted joint cutoffs -/

public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace WaveTurbulence.WeylSums

/-- Translating a joint cutoff multiplies its Fourier weight by a unit
linear phase and leaves its `L¹` norm unchanged. Thus the tensor-reduction
constant is uniform in all spatial cutoff shifts. -/
theorem exists_uniform_translated_fourier_representation {m : ℕ}
    (χ : EuclideanSpace ℝ (Fin m) → ℂ) (hc : HasCompactSupport χ)
    (hs : ContDiff ℝ ∞ χ) :
    ∃ F : EuclideanSpace ℝ (Fin m) → ℂ, Integrable F ∧
      ∀ a : EuclideanSpace ℝ (Fin m),
      ∃ Fₐ : EuclideanSpace ℝ (Fin m) → ℂ, Integrable Fₐ ∧
        (∫ ξ, ‖Fₐ ξ‖) = (∫ ξ, ‖F ξ‖) ∧
        ∀ x, χ (x-a) = ∫ ξ, Fₐ ξ * e (∑ i, ξ i * x i) := by
  obtain ⟨F, hF, hf⟩ := exists_compact_fourier_representation χ hc hs
  refine ⟨F, hF, ?_⟩
  intro a
  let Fₐ : EuclideanSpace ℝ (Fin m) → ℂ := fun ξ => F ξ * e (-(∑ i, ξ i * a i))
  have hFa : Integrable Fₐ := by
    apply hF.mul_bdd
    · exact (continuous_e.comp (by fun_prop)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun ξ => (norm_e _).le)
  refine ⟨Fₐ, hFa, ?_, ?_⟩
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ξ => by simp only [Fₐ, norm_mul, norm_e, mul_one])
  · intro x
    rw [hf]
    apply integral_congr_ae
    filter_upwards [] with ξ
    dsimp [Fₐ]
    rw [mul_assoc, ← e_add]
    congr 2
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end WaveTurbulence.WeylSums
