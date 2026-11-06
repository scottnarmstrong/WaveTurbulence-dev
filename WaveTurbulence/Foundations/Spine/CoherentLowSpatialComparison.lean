/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentKernelCodeErrorSum
public import WaveTurbulence.Foundations.Spine.CoherentAppSumSpatialNorm
public import WaveTurbulence.Foundations.Spine.RegularCodeReindex
/-! The full high-spatial-norm coherent comparison in the range where truncation equals the code sum. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset WaveTurbulence.Reg

 theorem coherent_low_order_spatial_comparison (P : WTParams)
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
    (t : ℝ) (ht : t ∈ Icc (p : ℝ) (p + 1)) :
    SNorm A (4 * m) (fun k => coherentCoupleSum P F (p + 1) (2 * n) t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) ≤
      ENNReal.ofReal (((12 ^ 9 : ℕ) ^ n : ℝ) *
        (((P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
          (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))) +
        ((2 : ℝ) ^ (2 * n + 1) *
          (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
            (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))))) := by
  classical
  let B : ℝ := ((12 ^ 9 : ℕ) ^ n : ℝ)
  let E₁ : ℝ := (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η))) *
    (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))
  let E₂ : ℝ := (2 : ℝ) ^ (2 * n + 1) *
    (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
      (ε * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))
  let e : Mom P.d → ℂ := fun k => ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
    (KQstar P.L P.γ P.δ F (uniformDecodedCouple p Q) t t k - Q.app P.δ p (F p) t t k)
  let a : Mom P.d → ℂ := fun k => (∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.size = 2 * n),
    Q.app P.δ p (fun x => P.φ (P.δ * p) x + R x) t t k) -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)
  have he : SNorm A (4 * m) e ≤ ENNReal.ofReal (B * E₁) :=
    coherent_kernel_code_error_SNorm_le P hsource hL hδ hC₁ hd hη.le ha hp hn A m hA F U C₂ hC₂
      hFlow hFhigh hmod D hD hchoice t ht
  have hApp : SNorm A (4 * m) a ≤ ENNReal.ofReal (B * E₂) :=
    coherent_app_sum_sub_taylor_SNorm_le P hsource htaylor hC₁ hδ hηmax hd hη ha hp hn A m hA R ε U
      hε hεC hU hφlow hφhigh hRhigh C₂ hC₂ hmod D hD hchoice t ht
  have hL0 : 0 < P.L := zero_lt_one.trans_le hL
  have hC0 : 0 < P.C₁ := zero_lt_one.trans_le hC₁
  have hE₁ : 0 ≤ B * E₁ := by dsimp only [B, E₁]; positivity
  have hE₂ : 0 ≤ B * E₂ := by dsimp only [B, E₂]; positivity
  have hsplit : (fun k => coherentCoupleSum P F (p + 1) (2 * n) t k -
      (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) = e + a := by
    funext k
    dsimp only [e, a, Pi.add_apply]
    rw [coherentCoupleSum_eq_codes P F p n hsmall t k]
    simp only [KQ]
    rw [hFp]
    letI := finite_coupleCodes n
    letI := Fintype.ofFinite {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n}
    simp only [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype, sum_sub_distrib]
    ring
  rw [hsplit]
  have hadd := SNorm_add_bound e a (contDiff_of_SNorm_bound hA e _ he)
    (contDiff_of_SNorm_bound hA a _ hApp) (B * E₁) (B * E₂) hE₁ hE₂ he hApp
  rw [← mul_add] at hadd
  exact hadd

end WaveTurbulence.LGSpine
