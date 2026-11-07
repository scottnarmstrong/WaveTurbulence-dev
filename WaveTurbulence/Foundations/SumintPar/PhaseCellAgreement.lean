/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.PhaseCellExtension

/-!
# Pointwise agreement for every fixed lattice phase extension

This supplies exact coefficientwise spatial recombination on the source
cube, using the same finite smooth time cells as the kernel norm proof.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace WaveTurbulence.SumintPar

/-- A fixed lattice phase agrees after finite cell recombination on the sheared cube. -/
theorem phase_timeCellExtension_agreement {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (x : D.S.VIdx → Fin d → ℤ) (r : Mom d)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (z : Fin 3 → ℝ)
    (hz : ∀ k, |z k| ≤ N) (ht : z 0 ∈ Icc (0:ℝ) N) :
    sourceOutputModulation D z * timeCellExtension D hI N h (D.phase L γ δ η x r 0) z =
      ∫ τ in D.timeDom hI (z 0) (z 1+z 0) (z 2+z 0), D.phase L γ δ η x r (z 0) τ := by
  classical
  have hc (j : ℤ) : sourceOutputModulation D z *
      (kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0) z *
        cellInverseExponential N h j z) =
      (timeCellProfile h j (z 0):ℂ) *
        (∫ τ in D.timeDom hI (z 0) (z 1+z 0) (z 2+z 0), D.phase L γ δ η x r (z 0) τ) := by
    unfold cellInverseExponential
    rw [inverseExponentialCutoff_eq_exp N z hz]
    by_cases hj : timeCellProfile h j (z 0) = 0
    · rw [hj,Complex.ofReal_zero]
      ring
    · have he := phaseIntegral_eq_localPhaseExtension D hI L γ δ η x r ((j:ℝ)*h) h
        (z 0) (z 1) (z 2) (abs_sub_cell_le_of_timeCellProfile_ne_zero hh j hj)
      have hv : ![z 0,z 1,z 2] = z := by ext k; fin_cases k <;> rfl
      rw [hv] at he
      rw [he]
      change _ = (timeCellProfile h j (z 0):ℂ) *
        ((sourceOutputModulation D z * (Real.exp (z 0-z 1-z 2):ℂ)) *
          kernelExtension D hI ((j:ℝ)*h) h (D.phase L γ δ η x r 0) z)
      ring
  unfold timeCellExtension
  rw [Finset.mul_sum]
  simp_rw [hc]
  rw [← Finset.sum_mul,← Complex.ofReal_sum,sum_timeCellProfile N hh ht,
    Complex.ofReal_one,one_mul]

/-- The fixed-input phase extension agrees at every point of the original source cube. -/
theorem phaseCellExtension_agreement {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (L γ δ η : ℝ)
    (x : D.S.VIdx → Fin d → ℤ) (r : Mom d) (t : Fin 3 → ℝ)
    (ht : ∀ j, t j ∈ Icc (0:ℝ) N) :
    phaseCellExtension D hI N h L γ δ η x r t =
      ∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x r (t 0) τ := by
  have he := phase_timeCellExtension_agreement D hI L γ δ η x r N hh
    (sourceTimeShear t) (abs_sourceTimeShear_le t ht) (ht 0)
  simpa [phaseCellExtension,sourceOutputModulation,sourceTimeShear] using he

end WaveTurbulence.SumintPar
