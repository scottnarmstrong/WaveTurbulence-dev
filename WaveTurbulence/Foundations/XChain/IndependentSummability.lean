/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.IndependentDecorationSums
/-! Absolute convergence of finite products of independent countable complex series. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset

theorem summable_independent_prod {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, Countable (β i)] (f : (i : ι) → β i → ℂ) (hf : ∀ i, Summable (f i)) :
    Summable (fun x : (i : ι) → β i => ∏ i, f i (x i)) := by
  classical
  let : ∀ i, MeasurableSpace (β i) := fun _ => ⊤
  have : ∀ i, MeasurableSingletonClass (β i) := fun _ => ⟨fun _ => trivial⟩
  have hcount : Measure.pi (fun i => (Measure.count : Measure (β i))) =
      (Measure.count : Measure ((i : ι) → β i)) := by
    apply Measure.ext_of_singleton
    intro x
    simp only [Measure.pi_singleton, Measure.count_singleton, prod_const_one]
  have hI := Integrable.fintype_prod_dep
    (μ := fun i => (Measure.count : Measure (β i)))
    (fun i => integrable_count_iff.mpr (hf i).norm)
  rw [hcount] at hI
  exact (integrable_count_iff.mp hI).of_norm

end WaveTurbulence.Induct
