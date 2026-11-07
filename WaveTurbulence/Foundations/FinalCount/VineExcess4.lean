/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess3
public import WaveTurbulence.Foundations.FinalCount.VineArith2
/-! Vine removal, part 12 (FINALCOUNT-G2): **DH23 Prop 9.4, Step 1, a VC formed by two double bonds** (L1801 last
sentence), conditional on the count `𝔉 ≲ L^d (RL)^d (L^{d-1} + δ⁻¹ min(R⁻¹ L^{d-2γ}, L^d)) (log L)^C`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

/-- The count `𝔉` for a VC formed by two double bonds: fix `(x₀, y₀)` (`L^d (ρL)^d` choices), then Lemma
`basiccount` (1) (L1801). -/
noncomputable def vineG (d : ℕ) (L γ δ R ρ Cf : ℝ) (e : ℕ) : ℝ :=
  Cf * L ^ d * (ρ * L) ^ d * (L ^ (d - 1) + δ⁻¹ * min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d)) * Real.log L ^ e

theorem L_alg1 (d : ℕ) {L γ : ℝ} (hd : 1 ≤ d) (hL : 0 < L) :
    L ^ d * L ^ d * L ^ (d - 1) * (L ^ (-((d : ℝ) - γ))) ^ 3 = L ^ (3 * γ - 1) := by
  have e1 : (L ^ (-((d : ℝ) - γ))) ^ 3 = L ^ (-((d : ℝ) - γ) * 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num
  have e2 : L ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
  have e3 : L ^ (d - 1) = L ^ (((d - 1 : ℕ) : ℝ)) := (Real.rpow_natCast L (d - 1)).symm
  rw [e1, e2, e3, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1
  push_cast [Nat.cast_sub hd]
  ring

theorem L_alg2 (d : ℕ) {L γ : ℝ} (hL : 0 < L) :
    L ^ d * L ^ d * L ^ ((d : ℝ) - 2 * γ) * (L ^ (-((d : ℝ) - γ))) ^ 3 = L ^ γ := by
  have e1 : (L ^ (-((d : ℝ) - γ))) ^ 3 = L ^ (-((d : ℝ) - γ) * 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; norm_num
  have e2 : L ^ d = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
  rw [e1, e2, ← Real.rpow_add hL, ← Real.rpow_add hL, ← Real.rpow_add hL]
  congr 1; ring

/-- The real inequality behind `vine_excess_double`. -/
theorem vine_real_double (d e : ℕ) {L γ δ C₁ R ρ Cf : ℝ} (hd : 1 ≤ d) (hL : 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 1 ≤ C₁) (hR : 0 < R) (hρ0 : 0 ≤ ρ) (hCf : 0 ≤ Cf) (hlog : 1 ≤ Real.log L) :
    ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℕ) : ℝ) *
        (rankFactor d L γ δ C₁ ((3 : ℕ) : ℤ) * Real.log L ^ 8) ≤
      Cf * (ρ ^ d * L ^ (3 * γ - 1) * Real.log L ^ (e + 8)) +
        δ⁻¹ * (Cf * (ρ ^ d * R⁻¹ * L ^ γ * Real.log L ^ (e + 8))) := by
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := by linarith
  have hq := qq_nonneg hδ.le (zero_le_one.trans hC)
  have hq1 := qq_le_one hδ hδ1 hC
  have hq3 : qq δ C₁ ^ 3 ≤ 1 := pow_le_one₀ hq hq1
  have hG0 : 0 ≤ vineG d L γ δ R ρ Cf e := by
    unfold vineG
    have : 0 ≤ min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) := le_min (by positivity) (by positivity)
    positivity
  have hN : ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℕ) : ℝ) ≤ vineG d L γ δ R ρ Cf e := Nat.floor_le hG0
  rw [rankFactor_nat d L γ δ C₁ hL0 3]
  have hrf : (L ^ (-((d : ℝ) - γ))) ^ 3 * qq δ C₁ ^ 3 ≤ (L ^ (-((d : ℝ) - γ))) ^ 3 := by
    have : 0 ≤ (L ^ (-((d : ℝ) - γ))) ^ 3 := by positivity
    nlinarith
  have hP8 : 0 ≤ Real.log L ^ 8 := by positivity
  have hpos : 0 ≤ (L ^ (-((d : ℝ) - γ))) ^ 3 * qq δ C₁ ^ 3 * Real.log L ^ 8 := by positivity
  have hmin : min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) ≤ R⁻¹ * L ^ ((d : ℝ) - 2 * γ) := min_le_left _ _
  have hA1 := L_alg1 d hd hL0 (γ := γ)
  have hA2 := L_alg2 d hL0 (γ := γ)
  calc ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℕ) : ℝ) * ((L ^ (-((d : ℝ) - γ))) ^ 3 * qq δ C₁ ^ 3 * Real.log L ^ 8)
      ≤ vineG d L γ δ R ρ Cf e * ((L ^ (-((d : ℝ) - γ))) ^ 3 * Real.log L ^ 8) := by
        calc _ ≤ vineG d L γ δ R ρ Cf e * ((L ^ (-((d : ℝ) - γ))) ^ 3 * qq δ C₁ ^ 3 * Real.log L ^ 8) :=
              mul_le_mul_of_nonneg_right hN hpos
          _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrf hP8) hG0
    _ = Cf * Real.log L ^ (e + 8) * ρ ^ d * (L ^ d * L ^ d * L ^ (d - 1) * (L ^ (-((d : ℝ) - γ))) ^ 3 +
          δ⁻¹ * (L ^ d * L ^ d * min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) * (L ^ (-((d : ℝ) - γ))) ^ 3)) := by
        unfold vineG; rw [mul_pow]; ring
    _ ≤ Cf * Real.log L ^ (e + 8) * ρ ^ d * (L ^ (3 * γ - 1) +
          δ⁻¹ * (R⁻¹ * L ^ γ)) := by
        rw [hA1]
        have h2 : L ^ d * L ^ d * min (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) (L ^ d) * (L ^ (-((d : ℝ) - γ))) ^ 3 ≤
            R⁻¹ * L ^ γ := by
          calc _ ≤ L ^ d * L ^ d * (R⁻¹ * L ^ ((d : ℝ) - 2 * γ)) * (L ^ (-((d : ℝ) - γ))) ^ 3 := by gcongr
            _ = R⁻¹ * (L ^ d * L ^ d * L ^ ((d : ℝ) - 2 * γ) * (L ^ (-((d : ℝ) - γ))) ^ 3) := by ring
            _ = R⁻¹ * L ^ γ := by rw [hA2]
        have : 0 ≤ Cf * Real.log L ^ (e + 8) * ρ ^ d := by positivity
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hδ.le))) this
    _ = _ := by ring

end WaveTurbulence.FinalCount
