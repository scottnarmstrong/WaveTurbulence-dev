/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentUniformKernelSpatialNorm
public import WaveTurbulence.Foundations.Spine.CoherentTruncatedSpatialNorm
public import WaveTurbulence.Foundations.Spine.CoherentSpatialTailArithmetic
public import WaveTurbulence.Foundations.Spine.CoherentTruncatedSpatialGeometric
public import WaveTurbulence.Foundations.Spine.MarkedGeometricTail
/-! Spatial bound for the actual coherent truncation, including its intermediate-order range. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg
 theorem coherent_truncated_tail_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hn1 : 1 ≤ n)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (B : ℝ) (hB : 0 ≤ B) (htail : P.N (p + 1) < 2 * n)
    (hlog : 2 * (B + 1) + 1 ≤ Real.log P.L)
    (hlarge : D * P.C₁ * (C₂ : ℝ) ^ (4 * m + A) ≤ P.L)
    (hsmall : (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
      (2 * P.C₁ ^ 2 * P.δ)) ≤ Real.sqrt P.δ * Real.exp (-1))
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (coherentCoupleSum P F (p + 1) (2 * n) t) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-B)) := by
  have hh := coherent_truncated_sum_geometric_SNorm_le P hsource hL hδ hC₁ hηmax hd hη ha hp hn hn1
    A m hA F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice t ht
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  exact marked_geometric_tail_le (by positivity) hδ.le (zero_lt_one.trans_le hL)
    (by positivity) hlarge hsmall n
    (tail_order_ge_log P hd (B + 1) (by linarith) hlog (p + 1) n htail)

end WaveTurbulence.LGSpine
