/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Fourier.PoissonMultidimensional
public import WaveTurbulence.Foundations.Probability.SchwartzLattice

/-!
# G7: the Schwartz lattice mass is bounded by `C L^d`

SEAL-PLAN §B.4 G7. Poisson summation extracts the exact volume factor.
The dual lattice has spacing at least one, so a fixed summable Schwartz
majorant bounds its Fourier samples uniformly over all `L ≥ 1`.
-/

public section

namespace WaveTurbulence.MainGlue
open Finset
open scoped Classical SchwartzMap

/-- Dual Schwartz samples have a summable majorant independent of the dilation. -/
theorem dual_samples_bound {d : ℕ} (f : 𝓢((Fin d → ℝ), ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L →
      Summable (fun n : Fin d → ℤ => ‖Fourier.timeFourier f (fun i => L * n i)‖) ∧
      (∑' n : Fin d → ℤ, ‖Fourier.timeFourier f (fun i => L * n i)‖) ≤ C := by
  let F := Fourier.coordinateFourierSchwartz f
  let K : ℝ := 2 ^ (2 * d - 1) *
    (SchwartzMap.seminorm ℂ 0 0 F + SchwartzMap.seminorm ℂ (2 * d) 0 F)
  let w : (Fin d → ℤ) → ℝ := fun n => (1 + ‖n‖) ^ (-((2 * d : ℕ) : ℤ))
  have hK : 0 ≤ K := mul_nonneg (by positivity) (add_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  have hw0 (n : Fin d → ℤ) : 0 ≤ w n := by dsimp [w]; positivity
  have hw : Summable w := summable_one_add_norm_zpow
  refine ⟨K * ∑' n, w n, mul_nonneg hK (tsum_nonneg hw0), ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith only [hL]
  have hb (n : Fin d → ℤ) : ‖Fourier.timeFourier f (fun i => L * n i)‖ ≤ K * w n := by
    have hn : ‖n‖ ≤ ‖(fun i => L * (n i : ℝ))‖ := by
      change ‖n‖ ≤ ‖L • (fun i => (n i : ℝ))‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hLpos, Fourier.norm_integerCast]
      exact le_mul_of_one_le_left (norm_nonneg _) hL
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖n‖) (add_le_add le_rfl hn) (2 * d)
    have h := (mul_le_mul_of_nonneg_right hp (norm_nonneg (F (fun i => L * n i)))).trans
      (Fourier.schwartz_polynomial_weight_le (2 * d) F _)
    change _ ≤ K at h
    dsimp only [w]
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + ‖n‖) _)).mpr
    simpa only [F, Fourier.coordinateFourierSchwartz_apply, mul_comm] using h
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb (hw.mul_left K)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, K * w n := hs.tsum_le_tsum hb (hw.mul_left K)
    _ = _ := tsum_mul_left

/-- Schwartz lattice samples form a genuine convergent series for every positive scale. -/
theorem summable_schwartz_lattice {d : ℕ} (φ : 𝓢(Mom d, ℝ)) {L : ℝ} (hL : 0 < L) :
    Summable (fun n : Fin d → ℤ => φ (latticePoint L n)) := by
  let f : 𝓢((Fin d → ℝ), ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm φ)
  have hs := Fourier.schwartz_lattice_summable (Fourier.schwartzCoordinateDilate hL.ne' f)
  apply Complex.summable_ofReal.mp
  apply hs.congr
  intro n
  change (φ (WithLp.toLp 2 (L⁻¹ • (fun i => (n i : ℝ)))) : ℂ) = (φ (latticePoint L n) : ℂ)
  congr 2
  ext i
  simp [latticePoint, div_eq_mul_inv, mul_comm]

/-- G7 in the frozen momentum carrier; the envelope need not be nonnegative. -/
theorem schwartz_lattice_sum_le {d : ℕ} (φ : 𝓢(Mom d, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 1 ≤ L →
      (∑' n : Fin d → ℤ, φ (latticePoint L n)) ≤ C * L ^ d := by
  let f : 𝓢((Fin d → ℝ), ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm φ)
  obtain ⟨C, hC, hbound⟩ := dual_samples_bound f
  refine ⟨C, hC, ?_⟩
  intro L hL
  have hLpos : 0 < L := by linarith only [hL]
  have hf (n : Fin d → ℤ) : f (fun i => (n i : ℝ) / L) = (φ (latticePoint L n) : ℂ) := rfl
  have hpoisson := Fourier.poisson_scaled_coordinates f hLpos
  simp_rw [hf] at hpoisson
  rw [← Complex.ofReal_tsum] at hpoisson
  have hn := congrArg norm hpoisson
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hLpos.le] at hn
  calc
    _ ≤ |∑' n : Fin d → ℤ, φ (latticePoint L n)| := le_abs_self _
    _ = L ^ d * ‖∑' n : Fin d → ℤ, Fourier.timeFourier f (fun i => L * n i)‖ := hn
    _ ≤ L ^ d * ∑' n : Fin d → ℤ, ‖Fourier.timeFourier f (fun i => L * n i)‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hbound hL).1) (pow_nonneg hLpos.le _)
    _ ≤ L ^ d * C := mul_le_mul_of_nonneg_left (hbound hL).2 (pow_nonneg hLpos.le _)
    _ = _ := mul_comm _ _

end WaveTurbulence.MainGlue
