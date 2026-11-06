/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FiniteCoverSum
public import WaveTurbulence.Foundations.XChain.SNormOperations
/-! Finite covering/counting assembly for the exact spatial seminorm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem SNorm_sum_le_cover_count {d A B : ℕ} {I J : Type*} [DecidableEq I]
    (s : Finset I) (t : Finset J) (S : J → Finset I) (f : I → Mom d → ℂ) (M N : J → ℝ)
    (hcover : ∀ i ∈ s, ∃ j ∈ t, i ∈ S j)
    (hf : ∀ i ∈ s, ContDiff ℝ A (f i))
    (hS : ∀ j ∈ t, ∀ i ∈ S j, ContDiff ℝ A (f i))
    (hM : ∀ j ∈ t, 0 ≤ M j) (hcount : ∀ j ∈ t, ((S j).card : ℝ) ≤ N j)
    (hbound : ∀ j ∈ t, ∀ i ∈ S j, SNorm A B (f i) ≤ ENNReal.ofReal (M j)) :
    SNorm A B (fun x => ∑ i ∈ s, f i x) ≤ ENNReal.ofReal (∑ j ∈ t, N j * M j) := by
  apply SNorm_le_of_momentum_bounds _ (ContDiff.sum hf)
  intro n hn ρ x
  have hderiv : Fourier.momentumDerivative ρ (fun x => ∑ i ∈ s, f i x) x =
      ∑ i ∈ s, Fourier.momentumDerivative ρ (f i) x := by
    unfold Fourier.momentumDerivative
    rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hf i hi).contDiffAt.of_le (by exact_mod_cast hn))]
    simp only [_root_.sum_apply]
  have hh := norm_sum_le_cover_count s t S
    (fun i => ((jbr x ^ B : ℝ) : ℂ) * Fourier.momentumDerivative ρ (f i) x)
    M N hcover hM hcount (by
      intro j hj i hi
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (jbr_pos x).le B)]
      exact SNorm_momentum_pointwise (f i) (hS j hj i hi) (M j) (hM j hj) (hbound j hj i hi) hn ρ x)
  rw [← mul_sum, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (jbr_pos x).le B)] at hh
  rw [hderiv]
  exact hh

end WaveTurbulence.LGSpine
