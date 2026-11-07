/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.KernelMassBound
public import WaveTurbulence.Foundations.SumintPar.PhaseCellExtension

/-!
# Uniform absolute time mass for all fixed-lattice-input extensions

Absolute phase norms are independent of the lattice inputs and external
momentum. The resulting finite bound is used only for countable Fubini;
it is never used as an oscillatory estimate.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace WaveTurbulence.SumintPar

/-- Every fixed-input phase extension has a common finite absolute time mass. -/
theorem exists_phaseCellExtension_mass_bound {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h L γ δ η : ℝ) (hη : η ≤ 1/3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : D.S.VIdx → Fin d → ℤ) (r : Mom d),
      (∫ t, ‖phaseCellExtension D hI N h L γ δ η x r t‖) ≤ C := by
  classical
  choose c hc using fun j : ℤ => (hasCompactSupport_cellInverseExponential N h j).exists_bound_of_continuous
    (contDiff_cellInverseExponential N h j).continuous
  let C := fun j => max 0 (c j)
  have hC (j : ℤ) : 0 ≤ C j := le_max_left _ _
  have hb (j : ℤ) (z : Fin 3 → ℝ) : ‖cellInverseExponential N h j z‖ ≤ C j :=
    (hc j z).trans (le_max_right _ _)
  let M := fun j : ℤ => ∫ u in localInputTimeDomain D ((j:ℝ)*h) h,
    ‖D.phase L γ δ η (fun _ => 0) 0 0 u‖
  have hM (j : ℤ) : 0 ≤ M j := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨∑ j ∈ timeCellIndices N h, C j*(2*M j),Finset.sum_nonneg (fun j _ => by positivity),?_⟩
  intro x r
  have hi (j : ℤ) : Integrable (kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0)) :=
    integrable_kernelExtension D hI _ h _ (measurable_phase D L γ δ η x r 0)
      (integrableOn_phase_localDomain D L γ δ η hη x r 0 _ h)
  have hik (j : ℤ) : Integrable (fun z => kernelExtension D hI ((j:ℝ)*h) h
      (D.phase L γ δ η x r 0) z*cellInverseExponential N h j z) :=
    (hi j).mul_bdd (contDiff_cellInverseExponential N h j).continuous.measurable.aestronglyMeasurable
      (ae_of_all _ (hb j))
  have hj (j : ℤ) : (∫ z, ‖kernelExtension D hI ((j:ℝ)*h) h
      (D.phase L γ δ η x r 0) z*cellInverseExponential N h j z‖) ≤ C j*(2*M j) := by
    calc
      _ ≤ ∫ z, ‖kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0) z‖*C j := by
        apply integral_mono (hik j).norm ((hi j).norm.mul_const _)
        intro z
        change ‖kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0) z*
          cellInverseExponential N h j z‖ ≤ _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb j z) (norm_nonneg _)
      _ = C j*(∫ z, ‖kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0) z‖) := by
        rw [integral_mul_const,mul_comm]
      _ ≤ C j*(2*M j) := by
        apply mul_le_mul_of_nonneg_left _ (hC j)
        have hh := integral_norm_kernelExtension_le D hI ((j:ℝ)*h) h _
          (measurable_phase D L γ δ η x r 0)
          (integrableOn_phase_localDomain D L γ δ η hη x r 0 _ h)
        simpa only [M,norm_phase] using hh
  have he : (fun t => ‖phaseCellExtension D hI N h L γ δ η x r t‖) =
      fun t => ‖timeCellExtension D hI N h (D.phase L γ δ η x r 0) (sourceTimeShear t)‖ := by
    funext t
    rw [phaseCellExtension,norm_mul,norm_sourceOutputModulation,one_mul]
  rw [he]
  rw [measurePreserving_sourceTimeShear.integral_comp sourceTimeShearEquiv.measurableEmbedding
    (fun z => ‖timeCellExtension D hI N h (D.phase L γ δ η x r 0) z‖)]
  calc
    _ ≤ ∫ z, ∑ j ∈ timeCellIndices N h, ‖kernelExtension D hI ((j:ℝ)*h) h
        (D.phase L γ δ η x r 0) z*cellInverseExponential N h j z‖ := by
      apply integral_mono
        (integrable_timeCellExtension D hI N h _ (measurable_phase D L γ δ η x r 0)
          (fun j => integrableOn_phase_localDomain D L γ δ η hη x r 0 _ h)).norm
        (integrable_finsetSum _ (fun j _ => (hik j).norm))
      intro z
      exact norm_sum_le _ _
    _ = ∑ j ∈ timeCellIndices N h, ∫ z, ‖kernelExtension D hI ((j:ℝ)*h) h
        (D.phase L γ δ η x r 0) z*cellInverseExponential N h j z‖ :=
      integral_finsetSum _ (fun j _ => (hik j).norm)
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hj j)

end WaveTurbulence.SumintPar
