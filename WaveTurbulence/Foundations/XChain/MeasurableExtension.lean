/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SolutionCongruence
public import WaveTurbulence.Foundations.XChain.MeasurableCoefficient
/-! Choosing an extension measurably while preserving every earlier outcome and time. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Set

theorem exists_measurable_solution_extension {d p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {L γ δ : ℝ} (hL : 0 < L) (φ : Mom d → ℝ)
    {g : (Fin d → ℤ) → Ω → ℂ} (hg : ∀ n, Measurable (g n))
    (F : Set Ω) (hF : MeasurableSet F)
    (old : Ω → ℝ → (Fin d → ℤ) → ℂ)
    (hmeasold : ∀ t ∈ Icc (0 : ℝ) p, ∀ n, Measurable fun ω => old ω t n)
    (hrapid : ∀ ω ∈ F, IsRapidDecay (initialCoeff L φ g ω))
    (hpoint : ∀ ω ∈ F, ∃ B : ℝ → (Fin d → ℤ) → ℂ,
      IsASolution L γ δ (p + 1) (initialCoeff L φ g ω) B ∧
      ∀ t ∈ Icc (0 : ℝ) p, B t = old ω t) :
    ∃ A : Ω → ℝ → (Fin d → ℤ) → ℂ,
      (∀ ω t, t ≤ (p : ℝ) → A ω t = old ω t) ∧
      (∀ t ∈ Icc (0 : ℝ) (p + 1), ∀ n, Measurable fun ω => A ω t n) ∧
      ∀ ω ∈ F, IsASolution L γ δ (p + 1) (initialCoeff L φ g ω) (A ω) := by
  classical
  let B := fun ω => if h : ω ∈ F then Classical.choose (hpoint ω h) else 0
  have hB (ω : Ω) (hω : ω ∈ F) :
      IsASolution L γ δ (p + 1) (initialCoeff L φ g ω) (B ω) ∧
      ∀ t ∈ Icc (0 : ℝ) p, B ω t = old ω t := by
    dsimp only [B]
    rw [dite_eq_left hω]
    exact Classical.choose_spec (hpoint ω hω)
  let A := fun ω t n => if t ≤ (p : ℝ) then old ω t n else F.indicator (fun ω => B ω t n) ω
  have hagree (ω : Ω) (t : ℝ) (ht : t ≤ (p : ℝ)) : A ω t = old ω t := by
    funext n
    exact ite_eq_left ht
  refine ⟨A, hagree, ?_, ?_⟩
  · intro t ht n
    by_cases htp : t ≤ (p : ℝ)
    · simpa only [A, ite_eq_left htp] using hmeasold t ⟨ht.1, htp⟩ n
    · have h := measurable_indicator_a_coefficient hL φ hg F hF B (fun ω hω => (hB ω hω).1)
        hrapid ht n
      simpa only [A, ite_eq_right htp] using h
  · intro ω hω
    apply isASolution_congr (by positivity) (hB ω hω).1
    intro t ht
    by_cases htp : t ≤ (p : ℝ)
    · exact (hagree ω t htp).trans ((hB ω hω).2 t ⟨ht.1, htp⟩).symm
    · funext n
      simp only [A, ite_eq_right htp, indicator_of_mem hω]

end WaveTurbulence.Induct
