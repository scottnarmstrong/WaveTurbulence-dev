/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VdCB.BProcessUniform
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Selecting the actual stationary frequencies

The set is defined by strict inequalities between actual endpoint
values of the derivative on the central interval. Intermediate value
proves the required stationary equations; they are not extra hypotheses.
-/

public section

open Set

namespace WaveTurbulence.VdCB

/-- Frequencies whose critical points lie at least `r` from both endpoints. -/
@[expose] noncomputable def stationaryFrequencies (f : ℝ → ℝ) (a b r : ℝ) (N : ℕ) : Finset ℤ :=
  (Finset.Icc 0 (N : ℤ)).filter (fun ν => deriv f (a + r) < ν ∧ (ν : ℝ) < deriv f (b - r))

theorem stationaryFrequencies_subset (f : ℝ → ℝ) (a b r : ℝ) (N : ℕ) :
    stationaryFrequencies f a b r N ⊆ Finset.Icc 0 (N : ℤ) := Finset.filter_subset _ _

/-- Actual critical points exist for every selected frequency. -/
theorem exists_stationary_centers {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b r : ℝ} (hab : a + r ≤ b - r) (N : ℕ) :
    ∃ c : ℤ → ℝ, ∀ ν ∈ stationaryFrequencies f a b r N,
      a ≤ c ν - r ∧ c ν + r ≤ b ∧ deriv f (c ν) = ν := by
  have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hex (ν : ℤ) : ∃ x : ℝ, ν ∈ stationaryFrequencies f a b r N →
      a ≤ x - r ∧ x + r ≤ b ∧ deriv f x = ν := by
    by_cases hν : ν ∈ stationaryFrequencies f a b r N
    · obtain ⟨_, hbounds⟩ := Finset.mem_filter.mp hν
      obtain ⟨x, hx, heq⟩ := intermediate_value_Icc hab hf1.continuous.continuousOn
        (show (ν : ℝ) ∈ Icc (deriv f (a + r)) (deriv f (b - r)) from ⟨hbounds.1.le, hbounds.2.le⟩)
      exact ⟨x, fun _ => ⟨by linarith [hx.1], by linarith [hx.2], heq⟩⟩
    · exact ⟨0, fun h => (hν h).elim⟩
  choose c hc using hex
  exact ⟨c, hc⟩

end WaveTurbulence.VdCB
