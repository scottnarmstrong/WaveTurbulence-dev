/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.FixedpointSolution
public import WaveTurbulence.Foundations.XChain.FixedpointGlue
public import WaveTurbulence.Foundations.XChain.InductParameters
public import WaveTurbulence.Foundations.XChain.MeasurableExtension
public import WaveTurbulence.Foundations.XChain.SolutionMomentIntegrability
/-! The analytic S1 step: one symmetric event, measurable classed extension, all signed moments. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory ProbabilityTheory Set
universe u

theorem nested_event_subset_zero {Ω : Type*} (F : ℕ → Set Ω) (p : ℕ)
    (hnest : ∀ q ≤ p, 1 ≤ q → F q ⊆ F (q - 1)) : F p ⊆ F 0 := by
  induction p with
  | zero => exact Subset.rfl
  | succ p ih =>
    have hsub : F (p + 1) ⊆ F p := by simpa using hnest (p + 1) le_rfl (by omega)
    exact hsub.trans (ih (fun q hq => hnest q (by omega)))

end WaveTurbulence.Induct
