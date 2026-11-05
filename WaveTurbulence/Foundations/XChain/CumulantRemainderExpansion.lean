/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantMultilinear
/-! Exact S6 expansion; every error choice contains at least one remainder coordinate. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open scoped ENNReal

theorem cumulant_add_error_terms {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : ι → Ω → ℂ)
    (hX : ∀ i, ∀ p : ℕ, 1 ≤ p → MemLp (X i) (p : ℝ≥0∞) μ)
    (hY : ∀ i, ∀ p : ℕ, 1 ≤ p → MemLp (Y i) (p : ℝ≥0∞) μ) :
    cumulant μ (fun i ω => X i ω + Y i ω) univ - cumulant μ X univ =
      ∑ f ∈ (univ : Finset (ι → Bool)).erase (fun _ => false),
        cumulant μ (fun i ω => if f i then Y i ω else X i ω) univ := by
  classical
  have h := cumulant_fintype_sum μ (fun i (b : Bool) ω => if b then Y i ω else X i ω) (by
    intro i b p hp
    cases b
    · exact hX i p hp
    · exact hY i p hp)
  have he : (fun i ω => ∑ b : Bool, if b then Y i ω else X i ω) =
      fun i ω => X i ω + Y i ω := by
    funext i ω
    simp [add_comm]
  rw [he] at h
  rw [h]
  have hs := Finset.sum_erase_add (s := (univ : Finset (ι → Bool))) (a := fun _ => false)
    (fun f => cumulant μ (fun i ω => if f i then Y i ω else X i ω) univ) (mem_univ _)
  simp only [Bool.false_eq_true, ite_false] at hs
  exact sub_eq_iff_eq_add.mpr hs.symm

/-- Each surviving Boolean choice has an actual remainder coordinate. -/
theorem remainder_choice_has_true {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → Bool}
    (hf : f ∈ (univ : Finset (ι → Bool)).erase (fun _ => false)) : ∃ i, f i = true := by
  have hne := (mem_erase.mp hf).1
  by_contra h
  push Not at h
  apply hne
  funext i
  exact Bool.eq_false_of_not_eq_true (h i)

end WaveTurbulence.Induct
