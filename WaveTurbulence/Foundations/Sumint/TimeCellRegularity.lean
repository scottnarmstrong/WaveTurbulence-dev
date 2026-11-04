/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.KernelLinearity
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Measurability, integrability and linearity of the actual finite cell sum

Compact smooth multipliers preserve genuine time integrability. These
facts justify the spatial Fourier recombination independently of gains.
-/

public section
open MeasureTheory
namespace WaveTurbulence.Sumint

/-- The finite cell extension is measurable for a measurable input. -/
theorem measurable_timeCellExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F) :
    Measurable (timeCellExtension D hI N h F) := by
  unfold timeCellExtension
  apply Finset.measurable_sum
  intro j _
  exact (measurable_kernelExtension D hI _ h F hF).mul
    (contDiff_cellInverseExponential N h j).continuous.measurable

/-- The finite cell extension satisfies genuine ambient time integrability. -/
theorem integrable_timeCellExtension {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) (h : ℝ) (F : (D.S.TVar → ℝ) → ℂ) (hF : Measurable F)
    (hFi : ∀ j : ℤ, IntegrableOn F (localInputTimeDomain D ((j:ℝ)*h) h)) :
    Integrable (timeCellExtension D hI N h F) := by
  unfold timeCellExtension
  apply integrable_finsetSum
  intro j _
  obtain ⟨C,hC⟩ := (hasCompactSupport_cellInverseExponential N h j).exists_bound_of_continuous
    (contDiff_cellInverseExponential N h j).continuous
  exact (integrable_kernelExtension D hI _ h F hF (hFi j)).mul_bdd
    (contDiff_cellInverseExponential N h j).continuous.measurable.aestronglyMeasurable (ae_of_all _ hC)

/-- The actual finite cell extension commutes with finite input sums. -/
theorem timeCellExtension_finsetSum {ι : Type*} {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) (s : Finset ι)
    (F : ι → (D.S.TVar → ℝ) → ℂ)
    (hFi : ∀ j ∈ s, ∀ k : ℤ, IntegrableOn (F j) (localInputTimeDomain D ((k:ℝ)*h) h))
    (z : Fin 3 → ℝ) :
    timeCellExtension D hI N h (fun u => ∑ j ∈ s, F j u) z =
      ∑ j ∈ s, timeCellExtension D hI N h (F j) z := by
  classical
  unfold timeCellExtension
  simp_rw [kernelExtension_finsetSum D hI _ h s F (fun j hj => hFi j hj _),Finset.sum_mul]
  exact Finset.sum_comm

end WaveTurbulence.Sumint
