/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew3
public import WaveTurbulence.Foundations.FinalCount.VCFinal
/-! # VINE-COUNT part 26 (session 4): the new-component count `vineFN` and the real assembly. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
open Finset
namespace WaveTurbulence.VineCount

/-- **The new-component label count** (TARGET excessprop1 (2)): `Cf ν δ⁻¹ L^{d-γ+γ₀} · C₂^m L^{(m-2)(d-γ)} δ^{-m/2}
(log L)^e / ∏ 𝔛_j^{z_j}`, i.e. the source's `L^{d-γ+γ₀+η³} L^{(m-2)(d-γ)} (C₁δ^{-1/2})^{m-1} ∏ 𝔛^{-z}` (L2177). -/
noncomputable def vineFN (d : ℕ) (L γ δ ν Cf C₂ Λ : ℝ) (m e : ℕ) : ℝ :=
  Cf * ν * δ⁻¹ * L ^ ((d : ℝ) - γ + min γ (1 - γ)) * (C₂ ^ m * L ^ (((m : ℝ) - 2) * ((d : ℝ) - γ)) *
    δ ^ (-(m : ℝ) / 2)) * Real.log L ^ e / Λ

theorem assemble_bad_new {m d : ℕ} {L δ γ Cp C₂ Λ Wp Bq : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hCp0 : 0 ≤ Cp) (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hBq : 0 ≤ Bq) (hΛ : 1 ≤ Λ) (hWp : 1 ≤ Wp)
    (hΛW : Λ ≤ Real.log L ^ 4 * Wp) :
    Bq * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) * 1 ≤
      Bq * ((C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2))) * (Real.log L ^ 4 / Λ) := by
  have hfb := final_bad (m := m) (E := 2 * ((d : ℝ) - γ)) d hL hδ0 hδ1 hCp0 hC₂ hCp rfl
  have hWp0 : 0 < Wp := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hinv : Wp⁻¹ ≤ Real.log L ^ 4 / Λ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hWp0 hΛ0]; nlinarith
  have h3 : (Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹ ≤
      (C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ) :=
    mul_le_mul hfb hinv (by positivity) (by positivity)
  calc Bq * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) * 1
      = Bq * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) := mul_one _
    _ ≤ Bq * ((C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ)) := mul_le_mul_of_nonneg_left h3 hBq
    _ = _ := by ring

theorem assemble_normal_new {m d : ℕ} {L δ γ Cp Ct C₂ Λ Wp Bq : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hCp0 : 0 ≤ Cp) (hCt0 : 0 ≤ Ct) (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hCt : Ct ≤ C₂) (hBq : 0 ≤ Bq)
    (hΛ : 1 ≤ Λ) (hWp : 1 ≤ Wp) (hΛW : Λ ≤ Real.log L ^ 4 * Wp) :
    Bq * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) *
      (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ))) ≤
      Bq * ((C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2))) * (Real.log L ^ 4 / Λ) := by
  have hfn := final_normal (m := m) (E := 2 * ((d : ℝ) - γ)) d hL hδ0 hδ1 hCp0 hCt0 hC₂ hCp hCt rfl
  have hWp0 : 0 < Wp := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hinv : Wp⁻¹ ≤ Real.log L ^ 4 / Λ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hWp0 hΛ0]; nlinarith
  have h3 : ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))) * Wp⁻¹ ≤
      (C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ) :=
    mul_le_mul hfn hinv (by positivity) (by positivity)
  calc Bq * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))
      = Bq * (((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))) * Wp⁻¹) := by ring
    _ ≤ Bq * ((C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ)) := mul_le_mul_of_nonneg_left h3 hBq
    _ = _ := by ring

end WaveTurbulence.VineCount
