/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WeylSums.GaussianSuperposition

/-! # Continuity of finite-amplitude exponential series -/

public section
open Finset
namespace WaveTurbulence.WeylSums

/-- A fixed finite amplitude permits continuous dependence on all phase
parameters, without any infinite-series convergence argument. -/
theorem continuous_finite_amplitude_sum {α X : Type*} [TopologicalSpace X]
    (A : α → ℂ) (hA : (Function.support A).Finite) (φ : X → α → ℝ)
    (hφ : ∀ a, Continuous (fun x => φ x a)) :
    Continuous (fun x => ∑' a, A a * e (φ x a)) := by
  classical
  let S := hA.toFinset
  have heq (x : X) : (∑' a, A a * e (φ x a)) = ∑ a ∈ S, A a * e (φ x a) := by
    apply tsum_eq_sum
    intro a ha
    have hz : A a = 0 := by
      by_contra hh
      exact ha (hA.mem_toFinset.mpr hh)
    rw [hz, zero_mul]
  simp_rw [heq]
  apply continuous_finsetSum
  intro a ha
  exact continuous_const.mul (continuous_e.comp (hφ a))

end WaveTurbulence.WeylSums
