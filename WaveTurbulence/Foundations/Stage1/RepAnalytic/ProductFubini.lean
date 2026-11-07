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

/-- **Product of superpositions.**  If `u_i(m) ` is dominated by a summable `W_i(m)` and sums to `s_i`, then
`∏_i u_i(m_i)` is summable over `Ξ = ∏ M_i` with sum `∏ s_i`. -/
theorem hasSum_prod_superposition {n : ℕ} {M : Fin n → Type*} (u : ∀ i, M i → ℂ) (W : ∀ i, M i → ℝ)
    (hW : ∀ i, Summable (W i)) (hu : ∀ i m, ‖u i m‖ ≤ W i m) (s : Fin n → ℂ)
    (hs : ∀ i, HasSum (u i) (s i)) :
    HasSum (fun m : ∀ i, M i => ∏ i, u i (m i)) (∏ i, s i) := by
  have hnorm : ∀ i, Summable fun m => ‖u i m‖ := fun i =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hu i) (hW i)
  have := (hasSum_pi_prod_dep n u hnorm).2
  simpa only [fun i => (hs i).tsum_eq] using this

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

/-- **Fubini against the counting measure on the mode space `Ξ`.**  The sum over `Ξ` inside an integral over
`X` is the integral over `Ξ` (counting measure) of the integrals over `X`, provided the total absolute
mass `∑_ξ ∫ |g ξ|` is finite. -/
theorem integral_tsum_eq_integral_count {X Ξ : Type*} [MeasurableSpace X] (μ : Measure X) [Countable Ξ]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ] (g : Ξ → X → ℂ)
    (hmeas : ∀ ξ, AEStronglyMeasurable (g ξ) μ) (hsum : ∑' ξ, ∫⁻ x, ‖g ξ x‖ₑ ∂μ ≠ ⊤) :
    ∫ x, ∑' ξ, g ξ x ∂μ = ∫ ξ, (∫ x, g ξ x ∂μ) ∂Measure.count ∧
      Integrable (fun ξ => ∫ x, g ξ x ∂μ) Measure.count := by
  have hint : ∀ ξ, Integrable (g ξ) μ := fun ξ => by
    refine ⟨hmeas ξ, ?_⟩
    have : ∫⁻ x, ‖g ξ x‖ₑ ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hsum (ENNReal.le_tsum (f := fun ξ => ∫⁻ x, ‖g ξ x‖ₑ ∂μ) ξ)
    exact lt_top_iff_ne_top.2 this
  have hnorm : Summable fun ξ => ‖∫ x, g ξ x ∂μ‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
      (ENNReal.summable_toReal hsum)
    rw [← integral_norm_eq_lintegral_enorm (hmeas ξ)]
    exact norm_integral_le_integral_norm _
  obtain ⟨hI, hE⟩ := integral_count_eq_tsum (fun ξ => ∫ x, g ξ x ∂μ) hnorm
  exact ⟨by rw [hE, integral_tsum hmeas hsum], hI⟩

end WaveTurbulence.RepAnalytic
