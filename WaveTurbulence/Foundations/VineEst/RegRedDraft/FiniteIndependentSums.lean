/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Absolutely convergent sums over finitely many independent discrete fibers -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open MeasureTheory

/-- Counting measure on a finite product of countable discrete fibers is the
product counting measure. This also handles empty fibers and an empty index. -/
theorem pi_count_eq_count {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableSingletonClass (β i)] [∀ i, Countable (β i)] :
    Measure.pi (fun i => (Measure.count : Measure (β i))) = (Measure.count : Measure ((i : ι) → β i)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp only [Measure.count_singleton,Finset.prod_const_one]

/-- Fubini for finite independent countable complex summable families, derived
through the ordinary product-counting-measure integral. -/
theorem tsum_pi_prod_complex {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Countable (β i)]
    (f : (i : ι) → β i → ℂ) (hf : ∀ i, Summable (f i)) :
    (∑' x : (i : ι) → β i, ∏ i, f i (x i)) = ∏ i, ∑' x, f i x := by
  let : (i : ι) → MeasurableSpace (β i) := fun _ => ⊤
  have (i : ι) : MeasurableSingletonClass (β i) := ⟨fun _ => MeasurableSet.of_discrete⟩
  have hfi (i : ι) : Integrable (f i) (Measure.count : Measure (β i)) :=
    integrable_count_iff.mpr (hf i).norm
  have hp := Integrable.fintype_prod_dep hfi
  have hc : Measure.pi (fun i => (Measure.count : Measure (β i))) =
      (Measure.count : Measure ((i : ι) → β i)) := pi_count_eq_count
  have ht : (∫ x : (i : ι) → β i, ∏ i, f i (x i) ∂Measure.pi (fun i => (Measure.count : Measure (β i)))) =
      ∑' x : (i : ι) → β i, ∏ i, f i (x i) := by
    rw [hc] at hp ⊢
    simpa only [Measure.real,Measure.count_singleton,ENNReal.toReal_one,one_smul] using integral_countable hp
  apply ht.symm.trans
  apply (integral_fintype_prod_eq_prod f).trans
  apply Finset.prod_congr rfl
  intro i _
  simpa only [Measure.real,Measure.count_singleton,ENNReal.toReal_one,one_smul] using integral_countable (hfi i)

end WaveTurbulence.RegRed
