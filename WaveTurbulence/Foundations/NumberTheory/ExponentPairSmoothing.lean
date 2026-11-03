/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.NumberTheory.FractionalSmoothing
import Mathlib.Tactic

/-!
# Optimized smoothing at an exponent-pair scale

A conditional numerical transfer from actual frequency bounds
`C * Q^lambda * n^kappa` and at most `D*Q` samples to sawtooth error
`Q^((kappa+lambda)/(1+kappa))`. No exponent-pair predicate is defined here;
NT-BPROC owns the shared phase-class and `IsExponentPair` API.
-/

public section

namespace WaveTurbulence.NumberTheory

/-- Optimizing the Fourier cutoff under a fractional frequency bound. The
frequency estimate is an explicit local hypothesis, and this is a distinct
conditional helper rather than a claim that an exponent pair is proved. -/
theorem abs_sum_sawtooth_le_of_frequency_scale {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {Q C D kappa lambda : ℝ} (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hk : 0 < kappa) (hk1 : kappa < 1) (hl : lambda ≤ 1)
    (hcard : (s.card:ℝ) ≤ D*Q)
    (hfreq : ∀ n : ℕ, 0 < n →
      ‖∑ i ∈ s, expPhase ((n:ℝ)*f i)‖ ≤ (C*Q^lambda)*(n:ℝ)^kappa) :
    |∑ i ∈ s, sawtooth (f i)| ≤
      (D/2+2*((Real.pi/kappa+1/(1-kappa))/Real.pi^2)*C)*
        Q^((kappa+lambda)/(1+kappa)) := by
  have hQp : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hkp : 0 < 1+kappa := by linarith only [hk]
  have hkden : 0 < 1-kappa := sub_pos.mpr hk1
  let eta : ℝ := (1-lambda)/(1+kappa)
  let e : ℝ := (kappa+lambda)/(1+kappa)
  let B : ℝ := (Real.pi/kappa+1/(1-kappa))/Real.pi^2
  have heta : 0 ≤ eta := div_nonneg (sub_nonneg.mpr hl) hkp.le
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcut : 1 ≤ Q^eta := Real.one_le_rpow hQ heta
  let H : ℕ := ⌈Q^eta⌉₊
  have hHlo : Q^eta ≤ (H:ℝ) := Nat.le_ceil _
  have hHposR : 0 < (H:ℝ) := zero_lt_one.trans_le (hcut.trans hHlo)
  have hH : 0 < H := by exact_mod_cast hHposR
  have hHhi : (H:ℝ) ≤ 2*Q^eta := by
    have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg hQp.le eta)
    change (H:ℝ) < Q^eta+1 at hh
    linarith only [hh,hcut]
  have he₁ : 1-eta = e := by
    dsimp only [eta,e]
    field_simp
    ring
  have he₂ : lambda+eta*kappa = e := by
    dsimp only [eta,e]
    field_simp
    ring
  have hquot : Q/Q^eta = Q^e := by
    calc
      _ = Q^((1:ℝ))/Q^eta := by rw [Real.rpow_one]
      _ = Q^(1-eta) := (Real.rpow_sub hQp 1 eta).symm
      _ = _ := by rw [he₁]
  have hprod : Q^lambda*Q^(eta*kappa) = Q^e := by
    rw [← Real.rpow_add hQp,he₂]
  have htwo : (2:ℝ)^kappa ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hk1.le
  have hHpow : (H:ℝ)^kappa ≤ 2*Q^(eta*kappa) := by
    calc
      _ ≤ (2*Q^eta)^kappa := Real.rpow_le_rpow (Nat.cast_nonneg H) hHhi hk.le
      _ = (2:ℝ)^kappa*Q^(eta*kappa) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hQp.le eta),← Real.rpow_mul hQp.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hQp.le _)
  have hA : 0 ≤ C*Q^lambda := mul_nonneg hC (Real.rpow_nonneg hQp.le _)
  have hs := abs_sum_sawtooth_le_of_rpow_exp_sum s f hA hk hk1 hH hfreq
  have hhead : (s.card:ℝ)/(2*H) ≤ (D/2)*Q^e := by
    calc
      _ ≤ (D*Q)/(2*H) := div_le_div_of_nonneg_right hcard (by positivity)
      _ ≤ (D*Q)/(2*Q^eta) := div_le_div_of_nonneg_left (mul_nonneg hD hQp.le)
        (by positivity) (mul_le_mul_of_nonneg_left hHlo zero_le_two)
      _ = (D/2)*(Q/Q^eta) := by ring
      _ = _ := by rw [hquot]
  have htail : B*(C*Q^lambda)*(H:ℝ)^kappa ≤ (2*B*C)*Q^e := by
    calc
      _ ≤ B*(C*Q^lambda)*(2*Q^(eta*kappa)) :=
        mul_le_mul_of_nonneg_left hHpow (mul_nonneg hB hA)
      _ = (2*B*C)*(Q^lambda*Q^(eta*kappa)) := by ring
      _ = _ := by rw [hprod]
  calc
    _ ≤ (s.card:ℝ)/(2*H)+B*(C*Q^lambda)*(H:ℝ)^kappa := hs
    _ ≤ (D/2)*Q^e+(2*B*C)*Q^e := add_le_add hhead htail
    _ = _ := by dsimp only [B,e]; ring

end WaveTurbulence.NumberTheory
