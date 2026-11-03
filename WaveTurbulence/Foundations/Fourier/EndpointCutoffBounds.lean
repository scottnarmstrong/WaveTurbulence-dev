/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Fourier.CutoffControl
public import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic

/-!
# Bounds for the output cutoffs and their derivatives

The original cutoff and its first derivative share the same support
radius. The cutoff control data therefore bound both endpoint factors
that arise when taking the diagonal time derivative.
-/

public section

open Set Function

namespace WaveTurbulence.Fourier

/-- Support and absolute-value bounds for one output cutoff factor. -/
structure EndpointCutoffBounds (a : ℝ → ℝ) (R C : ℝ) : Prop where
  eq_zero : ∀ t, R < |t| → a t = 0
  abs_le : ∀ t, |a t| ≤ C

/-- The topological support lies in the declared cutoff interval. -/
theorem CutoffControl.tsupport_subset {χ : ℝ → ℝ} (h : CutoffControl χ) :
    tsupport χ ⊆ Icc (-h.radius) h.radius := by
  change closure (support χ) ⊆ Icc (-h.radius) h.radius
  apply closure_minimal ?_ isClosed_Icc
  intro t ht
  have habs : |t| ≤ h.radius := by
    by_contra hn
    exact ht (h.eq_zero t (lt_of_not_ge hn))
  exact _root_.abs_le.mp habs

/-- The first derivative vanishes outside the same support radius. -/
theorem CutoffControl.deriv_eq_zero {χ : ℝ → ℝ} (h : CutoffControl χ) (t : ℝ)
    (ht : h.radius < |t|) : deriv χ t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hm
  exact (not_lt_of_ge (_root_.abs_le.mpr (h.tsupport_subset hm))) ht

/-- The second derivative also vanishes outside the same support radius. -/
theorem CutoffControl.second_deriv_eq_zero {χ : ℝ → ℝ} (h : CutoffControl χ) (t : ℝ)
    (ht : h.radius < |t|) : deriv (deriv χ) t = 0 := by
  apply deriv_of_notMem_tsupport
  intro hm
  exact (not_lt_of_ge (_root_.abs_le.mpr (h.tsupport_subset (tsupport_deriv_subset hm)))) ht

/-- Endpoint bounds for the original cutoff. -/
theorem CutoffControl.endpointBounds {χ : ℝ → ℝ} (h : CutoffControl χ) :
    EndpointCutoffBounds χ h.radius h.bound :=
  ⟨h.eq_zero, h.abs_le⟩

/-- Endpoint bounds for the first derivative cutoff use only scalar derivatives through order two. -/
theorem CutoffControl.deriv_endpointBounds {χ : ℝ → ℝ} (h : CutoffControl χ) :
    EndpointCutoffBounds (deriv χ) h.radius h.bound :=
  ⟨h.deriv_eq_zero, h.abs_deriv_le⟩

/-- The second derivative cutoff obeys the same scalar support and size bounds. -/
theorem CutoffControl.second_deriv_endpointBounds {χ : ℝ → ℝ} (h : CutoffControl χ) :
    EndpointCutoffBounds (deriv (deriv χ)) h.radius h.bound :=
  ⟨h.second_deriv_eq_zero, h.abs_second_deriv_le⟩

end WaveTurbulence.Fourier
