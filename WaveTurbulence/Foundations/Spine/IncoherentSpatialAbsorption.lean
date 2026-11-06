/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialGeometric
public import WaveTurbulence.Foundations.Spine.IncoherentAbsorption
/-! Numerical absorption after the full spatial transfer, with no high norm constant inside delta's base. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem SNorm_incoherentCoupleSum_absorbed (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hPC : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (C₁ C₂ U : NNReal)
    (hC₁ : (1 : ℝ) ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (hc : ∀ r ≤ p, ContDiff ℝ (40 * P.d + A : ℕ) (F r))
    (hlow : ∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (F r) ≤
      ENNReal.ofReal (C₁ : ℝ))
    (hhigh : ∀ r ≤ p, SNormR (40 * P.d + A) (40 * P.d + 4 * m) (F r) ≤
      ENNReal.ofReal (U : ℝ))
    (hcostC₂ : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1))
    (K : ℝ) (hK : 0 ≤ K)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ K * 8 ^ n)
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2)
    (hn1 : 1 ≤ n)
    (hsmall : (2 * P.C₁ * C₁) * ((12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) ≤ Real.sqrt P.δ)
    (c : ℝ)
    (hlarge : K * (C₂ : ℝ) ^ (4 * m + A) * (2 : ℝ) ^ (9 * p) *
      P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ P.L ^ (-c)) :
    SNorm A (4 * m) (incoherentCoupleSum P F (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-c)) := by
  have hh := SNorm_incoherentCoupleSum_geometric P hsource hd hL hη (zero_le_one.trans hPC) hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t ht K hK hchoice hr
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hpref := prefactor_pow_le
    (by nlinarith : 1 ≤ 2 * P.C₁ * (C₁ : ℝ))
    (by positivity : 0 ≤ (12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) hsmall hn1
  have hsqrt : Real.sqrt P.δ ^ n = P.δ ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hδ]
    congr 1
    ring
  rw [hsqrt] at hpref
  have he : (C₁ : ℝ) ^ (2 * n + 1) = (C₁ : ℝ) * ((C₁ : ℝ) ^ 2) ^ n := by
    rw [pow_succ, pow_mul]
    ring
  have halgebra :
      (2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))) =
      (2 * P.C₁ * C₁ * ((12 ^ 9 : ℝ) * 32 * P.C₁ * (C₁ : ℝ) ^ 2 * P.δ) ^ n) *
        (K * (C₂ : ℝ) ^ (4 * m + A) * (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) := by
    rw [he]
    simp only [mul_pow]
    have hpow : (4 : ℝ) ^ n * 8 ^ n = 32 ^ n := by rw [← mul_pow]; norm_num
    rw [← hpow]
    ring
  rw [halgebra]
  exact mul_le_mul hpref hlarge (by positivity) (Real.rpow_nonneg hδ _)

end WaveTurbulence.LGSpine
