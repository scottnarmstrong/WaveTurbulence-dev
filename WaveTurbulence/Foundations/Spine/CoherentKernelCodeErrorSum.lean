/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentConstantErrorNorm
public import WaveTurbulence.Foundations.Spine.RegularCodeSpatialSum
public import WaveTurbulence.Foundations.Spine.UniformRegularCouple
/-! Sum the actual uniform-layer kernel/app spatial errors over regular codes. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set WaveTurbulence.Reg

 theorem coherent_kernel_code_error_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hC₁ : 1 ≤ P.C₁)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (A m : ℕ) (hA : A ≠ 0) (F : ℕ → Mom P.d → ℝ) (U C₂ : NNReal) (hC₂ : (1 : ℝ) ≤ C₂)
    (hlow : SNormR (40 * P.d) (40 * P.d) (F p) ≤ ENNReal.ofReal P.C₁)
    (hhigh : SNormR (40 * P.d + 1 + A) (40 * P.d + 4 * m) (F p) ≤ ENNReal.ofReal (U : ℝ))
    (hmod : (((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d)) ^ (4 * m)) *
      ((P.d : ℝ) ^ (40 * P.d + A) * U) ≤ C₂)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ∀ G : Garden 2, G.IsPlain → G.order = 2 * n →
      ((inputLeaves G).card + 1 : ℝ) ^ A *
        (Fintype.card (RootWeightChoices G P.d m) : ℝ) ≤ D * 8 ^ n)
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
      (KQstar P.L P.γ P.δ F (uniformDecodedCouple p Q) t t k - Q.app P.δ p (F p) t t k)) ≤
      ENNReal.ofReal (((12 ^ 9 : ℕ) ^ n : ℝ) *
        ((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))) := by
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hC0 : 0 < P.C₁ := zero_lt_one.trans_le hC₁
  apply SNorm_finsum_codes_le hA n _ _ (by positivity)
  intro Q hwf hsize
  let LG := uniformDecodedCouple p Q
  have hcan : IsCanonC (p + 1) LG := uniformDecodedCouple_canonical p Q
  have hplain : LG.garden.IsPlain := hcan.1.1
  have horder : LG.garden.order = 2 * n := (decodedCouple_order Q).trans hsize
  have hcoh : IsCoherentCoupleAt p p p Q LG := isCoherentCoupleAt_of_canonical hcan hwf
    (uniformDecodedCouple_decodes p Q) (uniformDecodedCouple_incoherency p Q)
  exact coherent_uniform_error_SNorm_le P hsource hL hδ hC₁ hd hη ha hp hn Q LG hsize hcoh hplain
    horder (uniformDecodedCouple_layer p Q) A m F U C₂ hC₂ hlow hhigh hmod D
      (hchoice LG.garden hplain horder) t t ht ht

end WaveTurbulence.LGSpine
