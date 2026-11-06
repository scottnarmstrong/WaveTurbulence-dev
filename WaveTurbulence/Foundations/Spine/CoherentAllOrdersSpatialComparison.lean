/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentTailComparison
public import WaveTurbulence.Foundations.Spine.CoherentLowSpatialAbsorption
public import WaveTurbulence.Foundations.Spine.CoherentTruncatedSpatialTail
public import WaveTurbulence.Foundations.Spine.TaylorSpatialTail
public import WaveTurbulence.Foundations.Spine.SpatialDifferenceBounds
/-! TARGET L2253–2255: the coherent/Taylor spatial comparison above the full-code cutoff. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg
 theorem coherent_comparison_all_orders_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (htaylor : ∀ L ≥ P.L, SourceCoherentTaylorAt {P with L := L})
    (hL : 2 ≤ P.L) (hTaylor : TaylorBoundAt P) (hTC₂ : 0 ≤ P.C₂)
    (hTL : P.C₂ ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hηmax : P.η ≤ 1 / 2) (hd : 1 ≤ P.d) (hη : 0 < P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (m : ℕ) (hm : m = P.Lambda (p + 1)) (hA : 4 * m ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂) (hU : (1 : ℝ) ≤ U)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + (4 * m)) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + (4 * m)) * U) ≤ C₂)
    (R : Mom P.d → ℝ) (hFp : F p = fun x => P.φ (P.δ * p) x + R x)
    (ε : ℝ) (hε : 0 < ε) (hεC : ε ≤ P.C₁)
    (hφlow : SNormR (40 * P.d) (40 * P.d) (P.φ (P.δ * p)) ≤ ENNReal.ofReal P.C₁)
    (hφhigh : SNormR (40 * P.d + 1 + (4 * m)) (40 * P.d + 4 * m)
      (P.φ (P.δ * p)) ≤ ENNReal.ofReal (U : ℝ))
    (hRhigh : SNormR (40 * P.d + 1 + (4 * m)) (40 * P.d + 4 * m) R ≤ ENNReal.ofReal ε)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ (4 * m) *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (B : ℝ) (hB : 0 ≤ B)
    (hlog : 2 * ((B + 1) + 1) + 1 ≤ Real.log P.L)
    (hlarge : D * P.C₁ * (C₂ : ℝ) ^ (4 * m + (4 * m)) ≤ P.L)
    (hsmall : (P.C₁ + P.C₁ ^ 2) * (((((12 ^ 9) * 4 : ℕ) : ℝ) * 8 * P.C₁ ^ 2) *
      (2 * P.C₁ ^ 2 * P.δ)) ≤ Real.sqrt P.δ * Real.exp (-1))
    (hlowsmall : 64 * ((12 ^ 9 : ℕ) : ℝ) * P.C₁ ^ 4 * P.δ ≤ Real.sqrt P.δ)
    (hlowlarge : (2 * D * P.C₁ ^ 3 * (C₂ : ℝ) ^ (4 * m + (4 * m))) *
      (P.L ^ (-(P.gamma1 - Real.sqrt P.η)) + ε) ≤ P.L ^ (-B))
    (htsmall : P.C₁ * P.δ ≤ Real.sqrt P.δ * Real.exp (-1))
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm (4 * m) (4 * m) (fun k => coherentCoupleSum P F (p + 1) (2 * n) t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
      ENNReal.ofReal (P.δ ^ ((n : ℝ) / 2) * P.L ^ (-B)) := by
  by_cases hsmallorder : 2 * n ≤ P.N (p + 1)
  · exact coherent_low_order_SNorm_absorbed P hsource htaylor (by linarith) hC₁ hδ hηmax hd hη ha hp hn
      hsmallorder (4 * m) m hA F R hFp ε hε hεC U C₂ hU hC₂ hφlow hlow hφhigh hhigh hRhigh
      hmod D hD hchoice B hlowsmall hlowlarge t ht
  · have htail : P.N (p + 1) < 2 * n := by omega
    exact coherent_tail_comparison_SNorm_le P hsource hL hTaylor hTC₂ hTL hδ hC₁ hηmax hd hη.le ha
      hp hn (by omega) m hm hA F U C₂ hC₂ hU hlow hhigh hmod D hD hchoice B hB htail hlog
      hlarge hsmall htsmall t ht

end WaveTurbulence.LGSpine
