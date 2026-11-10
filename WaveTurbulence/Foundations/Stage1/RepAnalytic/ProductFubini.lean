/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.PiProdDep
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Joint superposition of several factors, and Fubini over the counting measure

The kernels `K*_Q`, `K*_T`, `K̃^U` of (redvine) are expanded separately (W6).  Their product is the
superposition over the product `Ξ = ∏_i M_i` of the mode types, with weight `∏_i w_i(m_i)`, amplitude
`∏_i a_i(m_i)` and phase `∏_i e^{πi m_i·t_i}`; the mass is the product of the masses.  The time integral and
the decoration sum are then exchanged with `∑_ξ` (Fubini against the counting measure on `Ξ`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic
open MeasureTheory
open scoped ENNReal

/-- The mass of the joint weight is the product of the masses. -/
theorem tsum_ofReal_prod {n : ℕ} {M : Fin n → Type*} (w : ∀ i, M i → ℝ) (hw : ∀ i m, 0 ≤ w i m) :
    ∑' m : ∀ i, M i, ENNReal.ofReal (∏ i, w i (m i)) = ∏ i, ∑' m, ENNReal.ofReal (w i m) := by
  have : ∀ m : ∀ i, M i, ENNReal.ofReal (∏ i, w i (m i)) = ∏ i, ENNReal.ofReal (w i (m i)) :=
    fun m => ENNReal.ofReal_prod_of_nonneg fun i _ => hw i (m i)
  simp_rw [this]
  exact ennreal_tsum_pi_prod_dep n (fun i m => ENNReal.ofReal (w i m))

/-- The integral against counting measure on a countable space is the sum. -/
theorem integral_count_eq_tsum {Ξ : Type*} [Countable Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (g : Ξ → ℂ) (hg : Summable fun ξ => ‖g ξ‖) :
    Integrable g Measure.count ∧ ∫ ξ, g ξ ∂Measure.count = ∑' ξ, g ξ := by
  have hint : Integrable g Measure.count := integrable_count_iff.2 hg
  refine ⟨hint, ?_⟩
  rw [integral_countable hint]
  refine tsum_congr fun ξ => ?_
  simp [measureReal_def]

theorem integral_count_real_eq_tsum {Ξ : Type*} [Countable Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (g : Ξ → ℝ) (hg : Summable fun ξ => ‖g ξ‖) :
    Integrable g Measure.count ∧ ∫ ξ, g ξ ∂Measure.count = ∑' ξ, g ξ := by
  have hint : Integrable g Measure.count := integrable_count_iff.2 hg
  refine ⟨hint, ?_⟩
  rw [integral_countable hint]
  refine tsum_congr fun ξ => ?_
  simp [measureReal_def]

end WaveTurbulence.RepAnalytic
