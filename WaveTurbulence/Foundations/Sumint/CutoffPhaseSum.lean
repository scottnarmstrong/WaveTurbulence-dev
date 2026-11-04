/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.InputCutoffLattice
public import WaveTurbulence.Foundations.Sumint.PhaseMeasurability
import Mathlib.Tactic

/-!
# The literal oscillatory lattice sum after inserting independent cutoffs

Its input frequencies are unrestricted. The cutoff support is finite
independently of those frequencies and all time variables. The crude
absolute bound below is used only to justify Fubini; oscillatory gains
are established separately.
-/

public section

open MeasureTheory Finset
open scoped ENNReal

namespace WaveTurbulence.Sumint

/-- The independent input modulation character after transposing the affine maps. -/
@[expose] noncomputable def inputCharacter {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) : ℂ :=
  ∏ v, (Real.fourierChar (inner ℝ (ν v) (latticePoint L (x v))) : ℂ)

/-- The exact localized oscillatory object to which the factor bounds apply. -/
@[expose] noncomputable def cutoffPhaseSum {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) : ℂ :=
  ∑' x : D.S.VIdx → Fin d → ℤ,
    ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ) *
      inputCharacter D L ν x * D.phase L γ δ η x r t τ

/-- Every independent input modulation has unit modulus. -/
theorem norm_inputCharacter {d : ℕ} (D : SumintDatum d) (L : ℝ)
    (ν : D.S.VIdx → Mom d) (x : D.S.VIdx → Fin d → ℤ) :
    ‖inputCharacter D L ν x‖ = 1 := by
  simp only [inputCharacter, norm_prod, Circle.norm_coe, prod_const_one]

/-- The cutoff product is between zero and one. -/
theorem inputCutoff_product_bounds {ι : Type*} [Fintype ι] {d : ℕ}
    (p : ι → Fin d → ℝ) (X : ι → Mom d) :
    0 ≤ (∏ v, inputCutoff (p v) (X v)) ∧ (∏ v, inputCutoff (p v) (X v)) ≤ 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => inputCutoff_nonneg _ _)
  · exact Finset.prod_le_one₀ (fun _ _ => inputCutoff_nonneg _ _)
      (fun _ _ => inputCutoff_le_one _ _)

/-- The localized source sum is literally finite, with a frequency-independent box. -/
theorem cutoffPhaseSum_eq_sum {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) :
    cutoffPhaseSum D L γ δ η p ν r t τ =
      ∑ x ∈ inputCutoffBox L p,
        ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ) *
          inputCharacter D L ν x * D.phase L γ δ η x r t τ := by
  unfold cutoffPhaseSum
  apply tsum_eq_sum
  intro x hx
  rw [inputCutoff_product_eq_zero hL p x hx, Complex.ofReal_zero, zero_mul, zero_mul]

/-- A uniform absolute bound for the actual finite source sum, before cancellation. -/
theorem norm_cutoffPhaseSum_le {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d)
    (t : ℝ) (τ : D.S.TVar → ℝ) :
    ‖cutoffPhaseSum D L γ δ η p ν r t τ‖ ≤
      ((inputCutoffBox L p).card : ℝ) * ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖ := by
  classical
  rw [cutoffPhaseSum_eq_sum D hL γ δ η p ν r t τ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _x ∈ inputCutoffBox L p, ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖ := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul, norm_mul, norm_inputCharacter, mul_one]
      have hb := inputCutoff_product_bounds p (fun v => latticePoint L (x v))
      have hc : ‖((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
      have hp : ‖D.phase L γ δ η x r t τ‖ = ‖D.phase L γ δ η (fun _ => 0) 0 t τ‖ := by
        simp_rw [norm_phase]
      rw [hp]
      exact mul_le_of_le_one_left (norm_nonneg _) hc
    _ = _ := by simp

/-- Measurability in the complete input-time vector. -/
theorem measurable_cutoffPhaseSum {d : ℕ} (D : SumintDatum d) {L : ℝ} (hL : 0 < L)
    (γ δ η : ℝ) (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d)
    (r : Mom d) (t : ℝ) : Measurable (cutoffPhaseSum D L γ δ η p ν r t) := by
  have he : cutoffPhaseSum D L γ δ η p ν r t = fun τ =>
      ∑ x ∈ inputCutoffBox L p,
        ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ) : ℂ) *
          inputCharacter D L ν x * D.phase L γ δ η x r t τ :=
    funext (cutoffPhaseSum_eq_sum D hL γ δ η p ν r t)
  rw [he]
  apply Finset.measurable_sum
  intro x _
  exact measurable_const.mul (measurable_phase D L γ δ η x r t)

end WaveTurbulence.Sumint
