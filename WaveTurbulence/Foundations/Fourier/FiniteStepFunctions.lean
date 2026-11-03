/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# Weighted finite step functions

Disjoint finite-measure sets identify finite weighted sequence norms with
function-space norms. This supplies the concrete finite-dimensional
realizations in the Riesz–Thorin proof of TARGET L2370.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Fourier

/-- A step function with prescribed coefficients on finitely many sets. -/
@[expose] noncomputable def finiteStepFunction {α : Type*} {n : ℕ}
    (A : Fin n → Set α) (a : Fin n → ℂ) (x : α) : ℂ :=
  ∑ i, (A i).indicator (fun _ => a i) x

/-- Disjointness makes the norm power of a step function a sum of norm powers. -/
theorem finiteStepFunction_norm_rpow {α : Type*} {n : ℕ}
    (A : Fin n → Set α) (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (a : Fin n → ℂ)
    {p : ℝ} (hp : 0 < p) (x : α) :
    ‖finiteStepFunction A a x‖ ^ p =
      ∑ i, (A i).indicator (fun _ => ‖a i‖ ^ p) x := by
  classical
  by_cases hx : ∃ i, x ∈ A i
  · obtain ⟨i, hi⟩ := hx
    have hother (j : Fin n) (hji : j ≠ i) : x ∉ A j :=
      fun hj => Set.disjoint_left.mp (hd hji) hj hi
    have hs : finiteStepFunction A a x = a i := by
      unfold finiteStepFunction
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        simp [hother j hji]
      · simp
    rw [hs, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      simp [hother j hji]
    · simp
  · have hx' : ∀ i, x ∉ A i := by simpa only [not_exists] using hx
    simp [finiteStepFunction, hx', Real.zero_rpow hp.ne']

/-- Finite step functions with finite-measure cells belong to every `Lᵖ`. -/
theorem finiteStepFunction_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} (A : Fin n → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hμ : ∀ i, μ (A i) ≠ ∞) (a : Fin n → ℂ) (p : ℝ≥0∞) :
    MemLp (finiteStepFunction A a) p μ := by
  unfold finiteStepFunction
  exact memLp_finsetSum Finset.univ fun i _ =>
    memLp_indicator_const p (hA i).nullMeasurableSet (a i) (Or.inr (hμ i))

/-- Integrability of finite step functions, including sets of zero measure. -/
theorem finiteStepFunction_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {n : ℕ} (A : Fin n → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hμ : ∀ i, μ (A i) ≠ ∞) (a : Fin n → ℂ) :
    Integrable (finiteStepFunction A a) μ :=
  memLp_one_iff_integrable.mp (finiteStepFunction_memLp A hA hμ a 1)

/-- The power integral of a disjoint step function is its finite weighted sum. -/
theorem finiteStepFunction_integral_norm_rpow {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (A : Fin n → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hμ : ∀ i, μ (A i) ≠ ∞) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (a : Fin n → ℂ) {p : ℝ} (hp : 0 < p) :
    (∫ x, ‖finiteStepFunction A a x‖ ^ p ∂μ) = ∑ i, μ.real (A i) * ‖a i‖ ^ p := by
  simp_rw [finiteStepFunction_norm_rpow A hd a hp]
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (hA _), smul_eq_mul]
  · intro i _
    exact (integrableOn_const (hμ i)).integrable_indicator (hA i)

/-- The real `Lᵖ` norm of a disjoint step function, as a weighted sequence norm. -/
theorem finiteStepFunction_lpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {n : ℕ} (A : Fin n → Set α) (hA : ∀ i, MeasurableSet (A i))
    (hμ : ∀ i, μ (A i) ≠ ∞) (hd : Pairwise (fun i j => Disjoint (A i) (A j)))
    (a : Fin n → ℂ) {p : ℝ} (hp : 0 < p) :
    lpNorm (finiteStepFunction A a) (ENNReal.ofReal p) μ =
      (∑ i, μ.real (A i) * ‖a i‖ ^ p) ^ p⁻¹ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) ENNReal.ofReal_ne_top
    (finiteStepFunction_memLp A hA hμ a (ENNReal.ofReal p)).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, finiteStepFunction_integral_norm_rpow A hA hμ hd a hp]

end WaveTurbulence.Fourier
