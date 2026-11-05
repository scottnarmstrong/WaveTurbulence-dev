/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopCoefficientBounds
/-! Unit-interval time boxes and source coupling prefactors in the finite top expansion. -/
public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory Set

theorem boxVol_le_one (T : TTree) {p t : ℝ} (hpt : p ≤ t) (ht : t ≤ p + 1) :
    SysAPI.boxVol T p t ≤ 1 := by
  unfold SysAPI.boxVol
  rw [measureReal_def, volume_pi_pi]
  simp only [Real.volume_Icc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.mpr hpt)]
  exact prod_le_one₀ (fun _ _ => sub_nonneg.mpr hpt) (fun _ _ => by linarith)

theorem norm_treePrefactor_le_one {d : ℕ} (L γ δ : ℝ) (T : TTree)
    (hc : |coupling d L γ δ| ≤ 1) : ‖SysAPI.treePrefactor L γ δ d T‖ ≤ 1 := by
  have hsign (ζ : ℤˣ) : ‖(((ζ : ℤ) : ℂ))‖ = 1 := by
    rcases Int.units_eq_one_or ζ with h | h <;> simp [h]
  unfold SysAPI.treePrefactor
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_prod, Complex.norm_I,
    hsign, prod_const_one, mul_one]
  exact pow_le_one₀ (abs_nonneg _) hc

theorem abs_coupling_le_one {d : ℕ} {L γ δ : ℝ} (hL : 1 ≤ L)
    (hγ : γ ≤ (d : ℝ)) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) : |coupling d L γ δ| ≤ 1 := by
  have hpow : 1 ≤ L ^ ((d : ℝ) - γ) :=
    Real.one_le_rpow hL (sub_nonneg.mpr hγ)
  have hden : 0 < 2 * L ^ ((d : ℝ) - γ) := by linarith
  unfold coupling
  rw [abs_div, abs_of_nonneg hδ, abs_of_pos hden]
  exact (div_le_one₀ hden).mpr (by linarith)

end WaveTurbulence.Induct
