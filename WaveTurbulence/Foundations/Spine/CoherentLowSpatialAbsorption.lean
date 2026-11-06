/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentLowSpatialComparison
public import WaveTurbulence.Foundations.Spine.CoherentSpatialAbsorption
/-! Low-order coherent spatial comparison after the two source parameter absorptions. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset

 theorem coherent_low_order_SNorm_absorbed (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (htaylor : ∀ L ≥ P.L, SourceCoherentTaylorAt {P with L := L})
    (hL : 1 ≤ P.L) (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 < P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hsmall : 2 * n ≤ P.N (p + 1))
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (R : Mom P.d → ℝ)
    (hFp : F p = fun x => P.φ (P.δ * p) x + R x)
    (ε : ℝ) (hε : 0 < ε) (hεC : ε ≤ P.C₁) (U C₂ : NNReal) (hU : (1 : ℝ) ≤ U) (hC₂ : (1 : ℝ) ≤ C₂)
    (hφlow : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal P.C₁)
    (hFlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hφhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (P.φ (P.δ * p)) ≤ ENNReal.ofReal (U : ℝ))
    (hFhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hRhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) R ≤ ENNReal.ofReal ε)
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A * (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (b : ℝ)
    (hsmallδ : 64 * ((12 ^ 9 : ℕ) : ℝ) * P.C₁ ^ 4 * P.δ ≤ Real.sqrt P.δ)
    (hlarge : (2 * D * P.C₁ ^ 3 * (C₂ : ℝ) ^ (4 * m + A)) *
      (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) + ε) ≤ P.L ^ (-b))
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => coherentCoupleSum P F (p + 1) (2 * n) t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
        ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-b)) := by
  have hh := coherent_low_order_spatial_comparison P hsource htaylor hL hC₁ hδ hηmax hd hη ha hp hn hsmall
    A m hA F R hFp ε hε hεC U C₂ hU hC₂ hφlow hFlow hφhigh hFhigh hRhigh hmod D hD hchoice t ht
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hb := coherent_spatial_prefactor_absorbed n (4 * m + A)
    (by positivity : (0 : ℝ) ≤ ((12 ^ 9 : ℕ) : ℝ)) hC₁ hδ.le hD (NNReal.coe_nonneg C₂)
    (Real.rpow_nonneg hL0.le _) hε.le hsmallδ hlarge
  simpa only [Nat.cast_pow] using hb

end WaveTurbulence.LGSpine
