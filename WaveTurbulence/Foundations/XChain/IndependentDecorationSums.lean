/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Normed.Module.FiniteDimension
/-! Products of independent countable complex sums, with totalized sums treated exactly. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem integral_count_eq_tsum_complex {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] (f : α → ℂ) :
    (∫ x, f x ∂Measure.count) = ∑' x, f x := by
  by_cases hs : Summable f
  · have hi : Integrable f Measure.count := integrable_count_iff.mpr hs.norm
    have he := integral_countable hi
    simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul] using he
  · have hi : ¬ Integrable f Measure.count := fun h => hs (integrable_count_iff.mp h).of_norm
    rw [integral_undef hi, tsum_eq_zero_of_not_summable hs]

theorem tsum_independent_prod {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Countable (β i)] (f : (i : ι) → β i → ℂ) :
    (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  classical
  let : ∀ i, MeasurableSpace (β i) := fun _ => ⊤
  have : ∀ i, MeasurableSingletonClass (β i) := fun _ => ⟨fun _ => trivial⟩
  have hcount : (Measure.pi (fun i => (Measure.count : Measure (β i)))) =
      (Measure.count : Measure ((i : ι) → β i)) := by
    apply Measure.ext_of_singleton
    intro x
    simp only [Measure.pi_singleton, Measure.count_singleton, Finset.prod_const_one]
  have he := integral_fintype_prod_eq_prod (μ := fun i => (Measure.count : Measure (β i))) f
  rw [hcount] at he
  exact (integral_count_eq_tsum_complex (fun x : (i : ι) → β i => ∏ i, f i (x i))).symm.trans
    (he.trans (Finset.prod_congr rfl (fun i _ => integral_count_eq_tsum_complex (f i))))

theorem tsum_sigma_independent_prod {α ι : Type*} [Fintype ι] {β : α → ι → Type*}
    [∀ a i, Countable (β a i)] (f : α → ℂ) (g : (a : α) → (i : ι) → β a i → ℂ)
    (hs : Summable (fun x : Σ a, (i : ι) → β a i => f x.1 * ∏ i, g x.1 i (x.2 i))) :
    (∑' x : Σ a, (i : ι) → β a i, f x.1 * ∏ i, g x.1 i (x.2 i)) =
      ∑' a, f a * ∏ i, ∑' b, g a i b := by
  apply hs.tsum_sigma.trans
  apply tsum_congr
  intro a
  change (∑' c : (i : ι) → β a i, f a * ∏ i, g a i (c i)) = f a * ∏ i, ∑' b, g a i b
  rw [tsum_mul_left]
  exact congrArg (fun z : ℂ => f a * z) (tsum_independent_prod (g a))

end WaveTurbulence.Induct
