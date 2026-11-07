/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Fourier.FourierL1Sobolev
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic
/-! Local jet bounds for a compactly supported chirp; C2-A, NOTES §3.1. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ContDiff FourierTransform
namespace WaveTurbulence.Cut2A
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A scalar character is the Fourier transform of a scalar Dirac mass. -/
theorem character_eq_dirac : (fun s : ℝ => (Real.fourierChar s : ℂ)) =
    VectorFourier.fourierIntegral Real.fourierChar (Measure.dirac (-1 : ℝ))
      (innerSL ℝ (E := ℝ)).toLinearMap₁₂ (fun _ => (1 : ℂ)) := by
  funext s
  simp [VectorFourier.fourierIntegral, Circle.smul_def]

theorem character_smooth : ContDiff ℝ ∞ (fun s : ℝ => (Real.fourierChar s : ℂ)) := by
  rw [character_eq_dirac]
  exact VectorFourier.contDiff_fourierIntegral (innerSL ℝ) (N := ⊤)
    (fun n _ => integrable_dirac (by simp))

/-- The derivative bound has no dependence on the evaluation point. -/
theorem character_jet_le (j : ℕ) (s : ℝ) :
    ‖iteratedFDeriv ℝ j (fun r : ℝ => (Real.fourierChar r : ℂ)) s‖ ≤ (2 * Real.pi) ^ j := by
  rw [character_eq_dirac, VectorFourier.iteratedFDeriv_fourierIntegral (innerSL ℝ)
    (N := (j : ℕ∞)) (fun n _ => integrable_dirac (by simp))
    aestronglyMeasurable_const (le_refl _)]
  simp only [VectorFourier.fourierIntegral, integral_dirac, Circle.norm_smul]
  apply (VectorFourier.norm_fourierPowSMulRight_le (innerSL ℝ)
    (fun _ : ℝ => (1 : ℂ)) (-1) j).trans
  simp only [norm_one, mul_one, norm_neg, one_pow, mul_one]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (by positivity) (norm_innerSL_le ℝ (E := ℝ))

/-- Finitely many jets are uniformly bounded on a fixed compact set. -/
theorem compact_jets_bounded {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : V → F} (hf : ContDiff ℝ ∞ f) {K : Set V} (hK : IsCompact K) (N : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ N, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have each (j : Fin (N + 1)) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ (j : ℕ) f x‖ ≤ C :=
    hK.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (by simp)).continuousOn
  choose c hc using each
  refine ⟨1 + ∑ j, |c j|, le_add_of_nonneg_right (sum_nonneg fun _ _ => abs_nonneg _), ?_⟩
  intro j hj x hx
  let i : Fin (N + 1) := ⟨j, by omega⟩
  have hi := single_le_sum (fun k (_ : k ∈ (univ : Finset (Fin (N + 1)))) => abs_nonneg (c k))
    (mem_univ i)
  exact (hc i x hx).trans ((le_abs_self _).trans (by linarith only [hi]))

/-- Uniform local chirp bound: only a polynomial in the scalar Fourier frequency is lost. -/
theorem chirp_jet_le {Q : V → ℝ} (hQ : ContDiff ℝ ∞ Q) {x : V} {C : ℝ}
    (hC : 1 ≤ C) {N : ℕ} (jets : ∀ j ≤ N, ‖iteratedFDeriv ℝ j Q x‖ ≤ C)
    (t : ℝ) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => (Real.fourierChar (t * Q y) : ℂ)) x‖ ≤
      (n.factorial : ℝ) * (1 + 2 * Real.pi) ^ N * ((1 + |t|) * C) ^ n := by
  have hd : 1 ≤ (1 + |t|) * C := one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (abs_nonneg t)) hC
  apply norm_iteratedFDeriv_comp_le character_smooth (contDiff_const.mul hQ) (by simp) x
  · intro j hj
    exact (character_jet_le j _).trans
      ((pow_le_pow_left₀ (by positivity) (by linarith : 2 * Real.pi ≤ 1 + 2 * Real.pi) j).trans
        (pow_le_pow_right₀ (by linarith [Real.pi_pos]) (hj.trans hn)))
  · intro j hj hjn
    change ‖iteratedFDeriv ℝ j (t • Q) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (hQ.contDiffAt.of_le (by simp)), norm_smul, Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (jets j (hjn.trans hn)) (abs_nonneg t)).trans
    apply (mul_le_mul_of_nonneg_right (by linarith only [abs_nonneg t] : |t| ≤ 1 + |t|)
      (zero_le_one.trans hC)).trans
    exact le_self_pow₀ hd (by omega)
end WaveTurbulence.Cut2A
