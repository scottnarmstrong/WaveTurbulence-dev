/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.WeightedKernelAgreement
public import WaveTurbulence.Foundations.Sumint.CellInverseExponential
public import WaveTurbulence.Foundations.Sumint.SourceTimeShear

/-!
# Exact recombination of the local time-cell kernels

The finite partition restores the original weighted source integral
on the complete output cube. Off a cell's support both sides vanish.
-/

public section
open MeasureTheory Set
namespace WaveTurbulence.Sumint

/-- The literal finite sum of the compact local source kernels. -/
@[expose] noncomputable def timeCellExtension {d : ℕ} (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) (h : ℝ) (F : (D.S.TVar → ℝ) → ℂ)
    (z : Fin 3 → ℝ) : ℂ :=
  ∑ j ∈ timeCellIndices N h,
    kernelExtension D hI ((j:ℝ)*h) h F z * cellInverseExponential N h j z

/-- Each cell reproduces its smooth partition contribution to the actual weighted integral. -/
theorem timeCell_kernel_agreement {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (j : ℤ) (z : Fin 3 → ℝ)
    (hz : ∀ k, |z k| ≤ N) :
    Complex.exp ((Real.pi*(∑ v, D.param v)*z 0 : ℝ)*Complex.I) *
      (kernelExtension D hI ((j:ℝ)*h) h (weightedCutoffInput D L γ δ η p ν r) z *
        cellInverseExponential N h j z) =
    (timeCellProfile h j (z 0):ℂ) *
      (((sourceWeightDecay D L γ η *
        ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ) *
        (∫ τ in D.timeDom hI (z 0) (z 1+z 0) (z 2+z 0),
          cutoffPhaseSum D L γ δ η p ν r (z 0) τ)) := by
  classical
  unfold cellInverseExponential
  rw [inverseExponentialCutoff_eq_exp N z hz]
  by_cases hj : timeCellProfile h j (z 0) = 0
  · rw [hj, Complex.ofReal_zero]
    ring
  · have ht := abs_sub_cell_le_of_timeCellProfile_ne_zero hh j hj
    have he := weighted_cutoffPhaseIntegral_eq_kernelExtension D hI L γ δ η p ν r
      ((j:ℝ)*h) h (z 0) (z 1) (z 2) ht
    have hv : ![z 0,z 1,z 2] = z := by ext k; fin_cases k <;> rfl
    rw [hv] at he
    rw [he]
    ring

/-- Summing the actual finite cells gives pointwise agreement on the full sheared source cube. -/
theorem timeCellExtension_agreement {d : ℕ} (D : SumintDatum d) (hI : 0 < D.S.I)
    (L γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (N : ℕ) {h : ℝ} (hh : 0 < h) (z : Fin 3 → ℝ)
    (hz : ∀ k, |z k| ≤ N) (ht : z 0 ∈ Icc (0:ℝ) N) :
    Complex.exp ((Real.pi*(∑ v, D.param v)*z 0 : ℝ)*Complex.I) *
      timeCellExtension D hI N h (weightedCutoffInput D L γ δ η p ν r) z =
    ((sourceWeightDecay D L γ η *
      ‖r‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ) *
      (∫ τ in D.timeDom hI (z 0) (z 1+z 0) (z 2+z 0),
        cutoffPhaseSum D L γ δ η p ν r (z 0) τ) := by
  classical
  unfold timeCellExtension
  rw [Finset.mul_sum]
  simp_rw [timeCell_kernel_agreement D hI L γ δ η p ν r N hh _ z hz]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, sum_timeCellProfile N hh ht,
    Complex.ofReal_one, one_mul]

end WaveTurbulence.Sumint
