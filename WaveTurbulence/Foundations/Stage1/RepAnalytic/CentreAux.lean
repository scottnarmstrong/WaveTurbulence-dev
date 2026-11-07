/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreSNorm

/-! # W5 auxiliaries: the node factor `χ_c` and pointwise bounds from `𝔖`-norms -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.RepAnalytic
open WaveTurbulence Finset
open scoped ContDiff ENNReal

/-- **The node factor**: `‖χ_n‖_{𝔖^{A,0}} ≤ C(d, A)` uniformly in `n` (TARGET (redvine2): `K_(𝔪)(k_𝔪)` is
supported in a unit ball with all derivatives up to `30d` bounded). -/
theorem snorm_chiC_le (d A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin d → ℤ, SNorm A 0 (chiC d n) ≤ ENNReal.ofReal C := by
  obtain ⟨C0, hC0, hC⟩ := chi0_jet_bound d A
  refine ⟨C0, hC0, fun n => Induct.SNorm_le_of_momentum_bounds _ (chiC_contDiff d n A) C0 ?_⟩
  intro k hk ρ x
  simp only [pow_zero, one_mul]
  refine (LGSpine.norm_momentumDerivative_le_frechet _ ρ x).trans ?_
  rw [norm_iteratedFDeriv_chiC, iteratedFDeriv_chi]
  exact hC k hk _

/-- A function of `𝔖`-norm `≤ 1` is pointwise bounded by `1`. -/
theorem norm_le_one_of_SNorm_le_one {d A B : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ A f)
    (h : SNorm A B f ≤ 1) (x : Mom d) : ‖f x‖ ≤ 1 := by
  have h1 : SNorm A B f ≤ ENNReal.ofReal 1 := by simpa using h
  have := LGSpine.SNorm_frechet_pointwise f hf 1 zero_le_one h1 (Nat.zero_le A) x
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at this
  have hj : (1 : ℝ) ≤ jbr x ^ B := one_le_pow₀ (Induct.one_le_jbr x)
  nlinarith [norm_nonneg (f x)]

/-- If `A ≠ 0` and `𝔖^{A,B}(f) < ⊤` then `f` is `C^A`. -/
theorem contDiff_of_SNorm_ne_top {d A B : ℕ} (hA : A ≠ 0) {f : Mom d → ℂ} (h : SNorm A B f ≠ ⊤) :
    ContDiff ℝ A f := by
  by_contra hc
  apply h
  unfold SNorm
  simp [hA, hc]

end WaveTurbulence.RepAnalytic
