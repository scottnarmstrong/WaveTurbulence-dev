/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib

/-! # PROT-OPS-TERM: an uncountable supremum of continuous functions, each a.e. below `Ψ`, is a.e. below `Ψ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

theorem ae_iSup_le_of_continuous {X ι : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) (f : ι → X → ℝ≥0∞) (hf : ∀ i, Continuous (f i))
    (Ψ : X → ℝ≥0∞) (h : ∀ i, ∀ᵐ x ∂μ, f i x ≤ Ψ x) : ∀ᵐ x ∂μ, ⨆ i, f i x ≤ Ψ x := by
  classical
  -- thresholds `ofReal q`, `q` rational, and basic open sets
  let Good : (Set X) × ℚ → Prop := fun p => ∃ i, ∀ y ∈ p.1, ENNReal.ofReal (p.2 : ℝ) < f i y
  let S : (Set X) × ℚ → Set X := fun p => if Good p then p.1 ∩ {y | Ψ y < ENNReal.ofReal (p.2 : ℝ)} else ∅
  have hS : ∀ p, μ (S p) = 0 := by
    intro p
    by_cases hg : Good p
    · obtain ⟨i, hi⟩ := hg
      simp only [S, if_pos (show Good p from ⟨i, hi⟩)]
      refine measure_mono_null (fun y hy => ?_) (ae_iff.1 (h i))
      simp only [mem_setOf_eq, not_le]
      exact hy.2.trans (hi y hy.1)
    · simp [S, hg]
  have hc : (({U | U ∈ countableBasis X} : Set (Set X)) ×ˢ (univ : Set ℚ)).Countable :=
    ((countable_countableBasis X).prod countable_univ)
  have hnull : μ (⋃ p ∈ (({U | U ∈ countableBasis X} : Set (Set X)) ×ˢ (univ : Set ℚ)), S p) = 0 :=
    (measure_biUnion_null_iff hc).2 fun p _ => hS p
  refine measure_mono_null (fun x hx => ?_) hnull
  have hx' : ∃ i, Ψ x < f i x := by simpa using hx
  obtain ⟨i, hi⟩ := hx'
  -- a rational threshold between
  obtain ⟨rr, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hi
  have hΨt : Ψ x ≠ ⊤ := ne_top_of_lt hr1
  have ha : (Ψ x).toReal < (rr : ℝ) := by
    have := (ENNReal.toReal_lt_toReal hΨt ENNReal.coe_ne_top).2 hr1
    simpa using this
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha
  have hq0 : 0 ≤ (q : ℝ) := (ENNReal.toReal_nonneg).trans hq1.le
  have hΨq : Ψ x < ENNReal.ofReal (q : ℝ) := by
    rw [← ENNReal.ofReal_toReal hΨt]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hq1)).2 hq1
  have hqf : ENNReal.ofReal (q : ℝ) < f i x := by
    refine lt_of_le_of_lt ?_ hr2
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hq2.le
  have hopen : IsOpen {y | ENNReal.ofReal (q : ℝ) < f i y} := isOpen_lt continuous_const (hf i)
  obtain ⟨U, hU, hxU, hUsub⟩ := (isBasis_countableBasis X).exists_subset_of_mem_open hqf hopen
  refine mem_biUnion (x := (U, q)) ⟨hU, mem_univ _⟩ ?_
  have hg : Good (U, q) := ⟨i, fun y hy => hUsub hy⟩
  simp only [S, if_pos hg]
  exact ⟨hxU, hΨq⟩

end WaveTurbulence.Flower.ProtOpsTerm
