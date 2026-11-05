/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.API
/-! Nonlinearity continuity needs only continuous coordinates and a uniform summable envelope. -/
public section
namespace WaveTurbulence.Induct
open MeasureTheory Complex Set Filter Topology
open NLS
open scoped ENNReal

theorem continuousOn_aNonlin_of_bound {d : ℕ} (L γ δ : ℝ)
    {a : ℝ → (Fin d → ℤ) → ℂ} {S : Set ℝ}
    (hc : ∀ n, ContinuousOn (fun t => a t n) S)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ S, ∀ n, ‖a t n‖ ≤ C * ((1 + ‖n‖) ^ (d + 1))⁻¹)
    (n : Fin d → ℤ) :
    ContinuousOn (fun s => aNonlin L γ δ 1 s (a s) (fun m => (starRingEnd ℂ) (a s m)) (a s) n) S := by
  simp_rw [SysAPI.aNonlin_eq_tsum_pairs]
  refine continuousOn_const.mul (continuousOn_tsum (fun q => ?_) (summable_cubic_majorant C hC0)
    (fun q s hs => ?_))
  · have h1 := hc q.1
    have h2 := (continuous_conj.comp_continuousOn (hc q.2))
    have h3 := hc (n - q.1 + q.2)
    have hph : Continuous fun s : ℝ => exp (((((1 : ℤ) : ℝ) * Real.pi * δ * L ^ (2 * γ) *
        resFactor (latticePoint L q.1) (latticePoint L q.2) (latticePoint L (n - q.1 + q.2)) (latticePoint L n) * s : ℝ) : ℂ) * I) := by fun_prop
    exact (((continuousOn_const.mul hph.continuousOn).mul h1).mul h2).mul h3
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      mul_one, Complex.norm_conj]
    have he := abs_epsCoef_le q.1 q.2 (n - q.1 + q.2)
    have h1 := hC s hs q.1
    have h2 := hC s hs q.2
    have h3 : ‖a s (n - q.1 + q.2)‖ ≤ C :=
      (hC s hs _).trans (mul_le_of_le_one_right hC0 (inv_one_add_norm_pow_le_one _))
    calc |epsCoef q.1 q.2 (n - q.1 + q.2)| * ‖a s q.1‖ * ‖a s q.2‖ * ‖a s (n - q.1 + q.2)‖
        ≤ 1 * ‖a s q.1‖ * ‖a s q.2‖ * ‖a s (n - q.1 + q.2)‖ := by gcongr; exact he
      _ ≤ 1 * (C * ((1 + ‖q.1‖) ^ (d + 1))⁻¹) * (C * ((1 + ‖q.2‖) ^ (d + 1))⁻¹) * C := by
          gcongr
      _ = _ := by ring


end WaveTurbulence.Induct
