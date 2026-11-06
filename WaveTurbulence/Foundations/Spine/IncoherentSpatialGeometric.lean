/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.IncoherentSpatialSum
public import WaveTurbulence.Foundations.Spine.IncoherentGeometricBound
/-! Evaluate the incoherency sum after the full spatial transfer. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

theorem SNorm_incoherentCoupleSum_geometric (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η) (hPC : 0 ≤ P.C₁) (hδ : 0 ≤ P.δ)
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
    (hr : (2 : ℝ) ^ (9 * p) * P.L ^ (-(P.gamma1 - Real.sqrt P.η)) ≤ 1 / 2) :
    SNorm A (4 * m) (incoherentCoupleSum P F (p + 1) (2 * n) t) ≤
      ENNReal.ofReal ((2 * P.C₁ * ((12 ^ 9 : ℝ) * 4 * P.C₁ * P.δ) ^ n * (2 : ℝ) ^ (9 * p) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) := by
  have hh := SNorm_incoherentCoupleSum_le_counted P hsource hd hL hη hPC hδ hp hn
    A m hA F C₁ C₂ U hC₁ hC₂ hc hlow hhigh hcostC₂ t ht K hK hchoice
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  let V : ℝ := K * 8 ^ n * ((C₁ : ℝ) ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))
  have he : (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
      (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
        ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g)) * V)) =
      (∑ g ∈ (range (n + 1)).filter (fun g => 1 ≤ g),
        (((12 ^ 9) ^ n * ((2 ^ (9 * p)) ^ g * 2 ^ (2 * n)) : ℕ) : ℝ) *
          (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g))) * V := by
    rw [sum_mul]
    apply sum_congr rfl
    intro g _
    ring
  change _ ≤ _ * V
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (counted_incoherent_sum_le (by linarith : 0 ≤ P.L) hPC hδ p n hr) (by dsimp [V]; positivity)

end WaveTurbulence.LGSpine
