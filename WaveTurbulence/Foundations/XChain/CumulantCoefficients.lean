/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantLinear
public import WaveTurbulence.Foundations.XChain.AllMoments
public import Mathlib.LinearAlgebra.Multilinear.Basic
/-! Finite random-variable spans and coordinate scalar multilinearity for T.cmattr. -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

theorem cumulant_update_mul {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (μ : Measure Ω) (X : ι → Ω → ℂ) (s : Finset ι) {i : ι} (hi : i ∈ s)
    (c : ℂ) (Y : Ω → ℂ) :
    cumulant μ (Function.update X i (fun ω => c * Y ω)) s =
      c * cumulant μ (Function.update X i Y) s := by
  have he : Function.update X i (fun ω => c * Y ω) =
      fun j ω => (if j = i then c else 1) * Function.update X i Y j ω := by
    funext j ω
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [he, cumulant_mul]
  have hp : (∏ j ∈ s, if j = i then c else 1) = c := by simp [hi]
  rw [hp]

noncomputable def linearFamily {Ω ι α : Type*} [Fintype α]
    (X : ι → α → Ω → ℂ) (c : ι → α → ℂ) : ι → Ω → ℂ :=
  fun i ω => ∑ a, c i a * X i a ω

theorem linearFamily_update {Ω ι α : Type*} [Fintype α] [DecidableEq ι]
    (X : ι → α → Ω → ℂ) (c : ι → α → ℂ) (i : ι) (v : α → ℂ) :
    linearFamily X (Function.update c i v) =
      Function.update (linearFamily X c) i (fun ω => ∑ a, v a * X i a ω) := by
  funext j ω
  by_cases hji : j = i
  · subst j
    simp [linearFamily]
  · simp [linearFamily, hji]

theorem linearFamily_memLp {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype α]
    {μ : Measure Ω} (X : ι → α → Ω → ℂ)
    (hX : ∀ i a, ∀ p : ℕ, 1 ≤ p → MemLp (X i a) (p : ℝ≥0∞) μ)
    (c : ι → α → ℂ) (i : ι) (p : ℕ) (hp : 1 ≤ p) :
    MemLp (linearFamily X c i) (p : ℝ≥0∞) μ :=
  memLp_finsetSum _ (fun a _ => (hX i a p hp).const_mul (c i a))

theorem integrable_prod_linearFamily {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype α]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : ι → α → Ω → ℂ)
    (hX : ∀ i a, ∀ p : ℕ, 1 ≤ p → MemLp (X i a) (p : ℝ≥0∞) μ)
    (c : ι → α → ℂ) (s : Finset ι) : Integrable (fun ω => ∏ i ∈ s, linearFamily X c i ω) μ :=
  integrable_prod_of_all_memLp _ s (fun i _ p hp => linearFamily_memLp X hX c i p hp)

end WaveTurbulence.Induct
