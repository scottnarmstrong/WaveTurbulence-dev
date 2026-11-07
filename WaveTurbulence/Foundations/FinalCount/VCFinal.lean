/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount2
public import WaveTurbulence.Foundations.FinalCount.VCExcess
/-! # VINE-COUNT part 20: the real inequalities comparing the chart count with `vineF'`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
open Finset
namespace WaveTurbulence.VineCount

theorem inv_pow_le_rpow_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (n : ℕ) {t : ℝ} (h : (n : ℝ) ≤ t) :
    δ⁻¹ ^ n ≤ δ ^ (-t) := by
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ1
  rw [Real.rpow_neg hδ0.le, ← Real.inv_rpow hδ0.le, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hδi h

/-- Bad vine: `s = 2m + 2` atoms. -/
theorem final_bad {m : ℕ} {L δ γ E Cp C₂ : ℝ} (d : ℕ) (hL : 1 ≤ L) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hCp0 : 0 ≤ Cp)
    (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hE : E = 2 * ((d : ℝ) - γ)) :
    (Cp * δ⁻¹ * L ^ E) ^ m ≤ C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
      δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2) := by
  have hL0 : 0 < L := by linarith
  have h1 : (Cp * δ⁻¹ * L ^ E) ^ m = Cp ^ m * δ⁻¹ ^ m * (L ^ (E * m)) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (L ^ E) m, ← Real.rpow_mul hL0.le]
  have h2 : L ^ (((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ))) = L ^ (E * m) := by
    congr 1; rw [hE]; push_cast; ring
  have h3 : δ⁻¹ ^ m ≤ δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2) := by
    have := inv_pow_le_rpow_neg hδ0 hδ1 m (t := ((2 * m + 2 : ℕ) : ℝ) / 2) (by push_cast; linarith)
    rw [neg_div]; exact this
  rw [h1, h2]
  have hp : Cp ^ m ≤ C₂ ^ (2 * m + 2) :=
    (pow_le_pow_left₀ hCp0 hCp m).trans (pow_le_pow_right₀ hC₂ (by omega))
  have hLp : 0 ≤ L ^ (E * m) := by positivity
  have hC20 : 0 ≤ C₂ ^ (2 * m + 2) := by positivity
  calc Cp ^ m * δ⁻¹ ^ m * L ^ (E * m) ≤ C₂ ^ (2 * m + 2) * δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2) * L ^ (E * m) := by
        gcongr
    _ = _ := by ring

/-- Normal vine: `s = 2m + 5` atoms. -/
theorem final_normal {m : ℕ} {L δ γ E Cp Ct C₂ : ℝ} (d : ℕ) (hL : 1 ≤ L) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hCp0 : 0 ≤ Cp) (hCt0 : 0 ≤ Ct) (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hCt : Ct ≤ C₂)
    (hE : E = 2 * ((d : ℝ) - γ)) :
    (Cp * δ⁻¹ * L ^ E) ^ m * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ))) ≤
      C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2) := by
  have hL0 : 0 < L := by linarith
  have h1 : (Cp * δ⁻¹ * L ^ E) ^ m = Cp ^ m * δ⁻¹ ^ m * (L ^ (E * m)) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (L ^ E) m, ← Real.rpow_mul hL0.le]
  have h2 : L ^ (((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ))) = L ^ (E * m) * L ^ (3 * ((d : ℝ) - γ)) := by
    rw [← Real.rpow_add hL0]; congr 1; rw [hE]; push_cast; ring
  have h3 : δ⁻¹ ^ (m + 2) ≤ δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2) := by
    have := inv_pow_le_rpow_neg hδ0 hδ1 (m + 2) (t := ((2 * m + 5 : ℕ) : ℝ) / 2) (by push_cast; linarith)
    rw [neg_div]; exact this
  rw [h1, h2]
  have hp : Cp ^ m * Ct ≤ C₂ ^ (2 * m + 5) := by
    calc Cp ^ m * Ct ≤ C₂ ^ m * C₂ := mul_le_mul (pow_le_pow_left₀ hCp0 hCp m) hCt hCt0 (by positivity)
      _ = C₂ ^ (m + 1) := by ring
      _ ≤ C₂ ^ (2 * m + 5) := pow_le_pow_right₀ hC₂ (by omega)
  have hLp : 0 ≤ L ^ (E * m) := by positivity
  have hLq : 0 ≤ L ^ (3 * ((d : ℝ) - γ)) := by positivity
  have hdd : δ⁻¹ ^ m * δ⁻¹ ^ 2 = δ⁻¹ ^ (m + 2) := by ring
  calc Cp ^ m * δ⁻¹ ^ m * L ^ (E * m) * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))
      = (Cp ^ m * Ct) * (δ⁻¹ ^ m * δ⁻¹ ^ 2) * (L ^ (E * m) * L ^ (3 * ((d : ℝ) - γ))) := by ring
    _ = (Cp ^ m * Ct) * δ⁻¹ ^ (m + 2) * (L ^ (E * m) * L ^ (3 * ((d : ℝ) - γ))) := by rw [hdd]
    _ ≤ C₂ ^ (2 * m + 5) * δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2) * (L ^ (E * m) * L ^ (3 * ((d : ℝ) - γ))) := by
        gcongr
    _ = _ := by ring

/-- Assembly, bad vine. -/
theorem assemble_bad {m d : ℕ} {L δ γ ρ Cp C₂ Λ Wp Rc N : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hCp0 : 0 ≤ Cp) (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hN : 0 ≤ N) (hρ0 : 0 ≤ ρ) (hρL : 1 ≤ ρ * L) (hRc0 : 0 ≤ Rc)
    (hRc : Rc ≤ (3 * (ρ * L)) ^ d) (hΛ : 1 ≤ Λ) (hWp : 1 ≤ Wp) (hΛW : Λ ≤ Real.log L ^ 4 * Wp) :
    Rc * ((N * (2 * L + 1) ^ d) * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) * 1) ≤
      vineF' d L γ δ ρ (N * 9 ^ d) C₂ Λ (2 * m + 2) 4 := by
  have hL0 : 0 < L := by linarith
  have hfb := final_bad (m := m) (E := 2 * ((d : ℝ) - γ)) d hL hδ0 hδ1 hCp0 hC₂ hCp rfl
  unfold vineF'
  have h2L : (2 * L + 1) ^ d ≤ (3 * L) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have hlogp : 0 ≤ Real.log L ^ 4 := by positivity
  have hWp0 : 0 < Wp := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hinv : Wp⁻¹ ≤ Real.log L ^ 4 / Λ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hWp0 hΛ0]; nlinarith
  have hA : 0 ≤ (Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m := by positivity
  have h3 : (Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹ ≤
      (C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ) :=
    mul_le_mul hfb hinv (by positivity) (by positivity)
  calc Rc * ((N * (2 * L + 1) ^ d) * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) * 1)
      ≤ (3 * (ρ * L)) ^ d * ((N * (3 * L) ^ d) * ((C₂ ^ (2 * m + 2) * L ^ ((((2 * m + 2 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 2 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ)) * 1) := by
        gcongr
    _ = _ := by
        push_cast
        rw [mul_pow, mul_pow, mul_pow, show (9 : ℝ) ^ d = 3 ^ d * 3 ^ d by rw [← mul_pow]; norm_num]
        ring

/-- Assembly, normal vine. -/
theorem assemble_normal {m d : ℕ} {L δ γ ρ Cp Ct C₂ Λ Wp Rc N : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) (hCp0 : 0 ≤ Cp) (hCt0 : 0 ≤ Ct) (hC₂ : 1 ≤ C₂) (hCp : Cp ≤ C₂) (hCt : Ct ≤ C₂) (hN : 0 ≤ N)
    (hρ0 : 0 ≤ ρ) (hρL : 1 ≤ ρ * L) (hRc0 : 0 ≤ Rc) (hRc : Rc ≤ (3 * (ρ * L)) ^ d) (hΛ : 1 ≤ Λ) (hWp : 1 ≤ Wp)
    (hΛW : Λ ≤ Real.log L ^ 4 * Wp) :
    Rc * ((N * (2 * L + 1) ^ d) * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) *
      (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))) ≤ vineF' d L γ δ ρ (N * 9 ^ d) C₂ Λ (2 * m + 5) 4 := by
  have hL0 : 0 < L := by linarith
  have hfn := final_normal (m := m) (E := 2 * ((d : ℝ) - γ)) d hL hδ0 hδ1 hCp0 hCt0 hC₂ hCp hCt rfl
  unfold vineF'
  have h2L : (2 * L + 1) ^ d ≤ (3 * L) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
  have hWp0 : 0 < Wp := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hinv : Wp⁻¹ ≤ Real.log L ^ 4 / Λ := by
    rw [inv_eq_one_div, div_le_div_iff₀ hWp0 hΛ0]; nlinarith
  have h3 : ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))) * Wp⁻¹ ≤
      (C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ) :=
    mul_le_mul hfn hinv (by positivity) (by positivity)
  calc Rc * ((N * (2 * L + 1) ^ d) * ((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m * Wp⁻¹) *
      (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ))))
      = Rc * ((N * (2 * L + 1) ^ d) * (((Cp * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) ^ m *
        (Ct * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ)))) * Wp⁻¹)) := by ring
    _ ≤ (3 * (ρ * L)) ^ d * ((N * (3 * L) ^ d) * ((C₂ ^ (2 * m + 5) * L ^ ((((2 * m + 5 : ℕ) : ℝ) - 2) * ((d : ℝ) - γ)) *
        δ ^ (-((2 * m + 5 : ℕ) : ℝ) / 2)) * (Real.log L ^ 4 / Λ))) := by
        gcongr
    _ = _ := by
        push_cast
        rw [mul_pow, mul_pow, mul_pow, show (9 : ℝ) ^ d = 3 ^ d * 3 ^ d by rw [← mul_pow]; norm_num]
        ring

end WaveTurbulence.VineCount
