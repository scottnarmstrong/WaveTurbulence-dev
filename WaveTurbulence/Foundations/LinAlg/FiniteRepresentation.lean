/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.LinAlg.LatticeRepresentation

/-!
# The finite-representation lemma with one uniform exponent

TARGET Lemma A.6 (`finitelem`, L2435–L2445), combining the representing-system
and finite-representative conclusions. The exponent is chosen before `L`, `M`,
and `k`, so it depends only on the dimension. We retain the documented ambient
large-box convention `2 ≤ L ≤ M`.
-/

public section

namespace WaveTurbulence.LinAlg
open scoped InnerProductSpace

/-- TARGET Lemma A.6, with both conclusions and one dimension-dependent exponent. -/
theorem exists_uniform_finite_lattice_representation (d : ℕ) :
    ∃ C₀ : ℕ,
      (∀ L M : ℝ, 2 ≤ L → L ≤ M → ∀ k : Fin d → ℤ,
        ∃ q ≤ d, ∃ v : Fin q → Fin d → ℤ, ∃ m : Fin q → ℤ,
          (∀ i, latticePoint L (v i) ≠ 0) ∧
          (Pairwise fun i j => ⟪latticePoint L (v i), latticePoint L (v j)⟫_ℝ = 0) ∧
          (∀ i, ‖latticePoint L (v i)‖ ≤ M ^ C₀) ∧
          ‖latticePoint (L ^ 2) m‖ ≤ M ^ C₀ ∧
          (∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
            |⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M →
            latticePoint L z ∈ Submodule.span ℝ (Set.range fun i => latticePoint L (v i))) ∧
          (∀ γ : Fin q → ℝ,
            ⟪latticePoint L k, ∑ i, γ i • latticePoint L (v i)⟫_ℝ =
              ∑ i, ((m i : ℝ) / L ^ 2) * γ i)) ∧
      (∀ L M : ℝ, 2 ≤ L → L ≤ M → ∃ R : Finset (Mom d),
        (∀ k ∈ R, ∃ n : Fin d → ℤ, k = latticePoint L n) ∧
        (R.card : ℝ) ≤ M ^ C₀ ∧
        ∀ k : Fin d → ℤ, ∃ k' ∈ R, ∀ z : Fin d → ℤ, ‖latticePoint L z‖ ≤ M →
          (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M ↔
            |⟪k', latticePoint L z⟫_ℝ| ≤ M) ∧
          (|⟪latticePoint L k, latticePoint L z⟫_ℝ| ≤ M →
            ⟪latticePoint L k, latticePoint L z⟫_ℝ = ⟪k', latticePoint L z⟫_ℝ)) := by
  let C₀ := max (representationHeightExponent d) (4 * d * d + 6 * d)
  refine ⟨C₀, ?_, ?_⟩
  · intro L M hL hLM k
    obtain ⟨q, hq, v, m, h0, horth, hnorm, hm, hspan, hinner⟩ :=
      exists_lattice_representation hL hLM k
    have hpow : M ^ representationHeightExponent d ≤ M ^ C₀ :=
      pow_le_pow_right₀ (by linarith : 1 ≤ M) (le_max_left _ _)
    exact ⟨q, hq, v, m, h0, horth, fun i => (hnorm i).trans hpow, hm.trans hpow, hspan, hinner⟩
  · intro L M hL hLM
    obtain ⟨R, hRl, hcard, hrep⟩ := exists_lattice_representatives (d := d) hL hLM
    have hpow : M ^ (4 * d * d + 6 * d) ≤ M ^ C₀ :=
      pow_le_pow_right₀ (by linarith : 1 ≤ M) (le_max_right _ _)
    exact ⟨R, hRl, hcard.trans hpow, hrep⟩

end WaveTurbulence.LinAlg
