/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CoupleRemainderSumBound
public import WaveTurbulence.Foundations.XChain.WkeTaylorTailBound
public import WaveTurbulence.Foundations.XChain.SNormAddBounds
/-! The next real remainder has an explicit spatial-norm bound from exactly the two deterministic gates. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset Set
open scoped ENNReal

noncomputable def nextRemainder (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (p Ncut : ℕ) (t : ℝ) : Mom P.d → ℝ := fun k =>
  (∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k).re -
    wkeTaylorTail P p (Ncut / 2 + 1) t k

theorem nextRemainder_SNormR_bound (P : WTParams) (hG : LayergardenBody P) (hW : WkeTaylorBody P)
    (R : ℕ → Mom P.d → ℝ) (p : ℕ) (hp : p < P.D) (hR : RemainderBound P R p)
    (hd : 1 ≤ P.d) (hL : 0 < P.L) (hδ : 0 < P.δ) (hC : 0 ≤ P.C₂)
    (hsmall : P.δ ^ (2 * P.ν) ≤ 1 / 2)
    (hr : 0 ≤ P.C₁ * P.δ) (hr1 : P.C₁ * P.δ < 1)
    (Ncut : ℕ) (hcut : Ncut ≤ P.N (p + 1) ^ 4)
    (t : ℝ) (ht : t ∈ Ioc (p : ℝ) (p + 1)) :
    SNormR (P.Lambda (p + 1)) (P.Lambda (p + 1)) (nextRemainder P R p Ncut t) ≤
      ENNReal.ofReal (2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) +
        P.C₂ * (P.C₁ * P.δ) ^ (Ncut / 2 + 1) / (1 - P.C₁ * P.δ)) := by
  let A := 4 * P.Lambda (p + 1)
  let f : Mom P.d → ℂ := fun k => ∑ N ∈ range (Ncut + 1), coupleRemainder P R p N t k
  let g : Mom P.d → ℂ := fun k => (wkeTaylorTail P p (Ncut / 2 + 1) t k : ℂ)
  let C : ℝ := 2 * P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5)
  let D : ℝ := P.C₂ * (P.C₁ * P.δ) ^ (Ncut / 2 + 1) / (1 - P.C₁ * P.δ)
  have hA : A ≠ 0 := by
    have h := lambda_succ_ge P hd hp
    dsimp [A]
    omega
  have hC0 : 0 ≤ C := mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _)
  have hD0 : 0 ≤ D := div_nonneg (mul_nonneg hC (pow_nonneg hr _)) (sub_pos.mpr hr1).le
  have hfbound : SNorm A A f ≤ ENNReal.ofReal C :=
    coupleRemainder_sum_SNorm_bound P hG R p hp hR hd hL hδ hsmall Ncut hcut t ht
  have hgbound : SNorm A A g ≤ ENNReal.ofReal D :=
    wkeTaylorTail_SNormR_bound P hW hd p hp hC hr hr1 (Ncut / 2 + 1) t ⟨ht.1.le, ht.2⟩
  have hf := contDiff_of_SNorm_bound hA f C hfbound
  have hg := contDiff_of_SNorm_bound hA g D hgbound
  have hs : SNorm A A (f + -g) ≤ ENNReal.ofReal (C + D) :=
    SNorm_add_bound f (-g) hf hg.neg C D hC0 hD0 hfbound (SNorm_neg_bound g hg D hD0 hgbound)
  have hlow : P.Lambda (p + 1) ≤ A := by dsimp [A]; omega
  have hs' := SNorm_mono_bound hlow hlow (f + -g) (hf.add hg.neg) (C + D) (add_nonneg hC0 hD0) hs
  have hreal := SNormR_realPart_bound (f + -g) ((hf.add hg.neg).of_le (by exact_mod_cast hlow))
    (C + D) (add_nonneg hC0 hD0) hs'
  have he : nextRemainder P R p Ncut t = fun k => ((f + -g) k).re := by
    funext k
    simp [nextRemainder, f, g, sub_eq_add_neg]
  rw [he]
  exact hreal

end WaveTurbulence.Induct
